(function () {
  "use strict";

  const SUITS = ["d", "h", "k", "s"];
  const RANKS = [
    "01", "02", "03", "04", "05", "06", "07", "08", "09", "10", "11", "12", "13",
  ];
  const IMG_DIR = "playingcard_png/type-B/";
  /** CPUが標準局面で読む先読み深さ */
  const CPU_SEARCH_DEPTH = 3;
  /** 終盤（候補が少ない）で使う深い探索 */
  const CPU_SEARCH_DEPTH_ENDGAME = 5;
  /** 未開示プールを全列挙で評価する上限（これ以下は全件評価） */
  const CPU_MAX_POOL_ENUMERATE = 18;
  /** 未開示プールが大きいとき層化サンプルで近似評価する件数 */
  const CPU_MAX_POOL_SAMPLES = 24;
  /** 既知札候補が多いとき評価する最大件数 */
  const CPU_MAX_SLOT_BRANCH = 20;
  /** CPU 1ターンあたりの思考時間上限（ms） */
  const CPU_THINK_BUDGET_MS = 3000;
  const SHUFFLE_REDEAL_MS = 280;
  const BOARD_COLS = 13;
  const BOARD_ROWS = 4;

  /** @returns {string[]} */
  function buildDeck() {
    const deck = [];
    for (const s of SUITS) {
      for (const r of RANKS) {
        deck.push(s + r);
      }
    }
    return deck;
  }

  function shuffle(arr) {
    const a = arr.slice();
    for (let i = a.length - 1; i > 0; i--) {
      const j = Math.floor(Math.random() * (i + 1));
      [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
  }

  /** multiset pool から key を1枚除去したコピー */
  function removeOneKeyFromPool(pool, key) {
    const i = pool.indexOf(key);
    if (i === -1) return pool.slice();
    return pool.slice(0, i).concat(pool.slice(i + 1));
  }

  /** 候補が多すぎるとき評価コストを抑えるためのサンプル（保険） */
  function sampleSlotIndicesForCpu(indices) {
    if (indices.length <= CPU_MAX_SLOT_BRANCH) return indices;
    return shuffle(indices.slice()).slice(0, CPU_MAX_SLOT_BRANCH);
  }

  // 未知伏せ札は期待値的に同質なので代表1枚のみ評価し、既知札を厚く読む。
  function buildCpuCandidateIndices(indicesAll) {
    const known = [];
    const unknown = [];
    for (let i = 0; i < indicesAll.length; i++) {
      const idx = indicesAll[i];
      if (slots[idx].everRevealed) known.push(idx);
      else unknown.push(idx);
    }
    const knownSampled =
      known.length <= CPU_MAX_SLOT_BRANCH
        ? known
        : shuffle(known).slice(0, CPU_MAX_SLOT_BRANCH);
    if (!unknown.length) return knownSampled;
    return knownSampled.concat([unknown[0]]);
  }

  /** 候補数に応じてCPU探索深さを調整（終盤ほど深く読む） */
  function cpuDepthForState(candidateCount) {
    if (candidateCount <= 4) return CPU_SEARCH_DEPTH_ENDGAME;
    if (candidateCount <= 8) return CPU_SEARCH_DEPTH + 1;
    return CPU_SEARCH_DEPTH;
  }

  /**
   * 既知伏せ札だけで 21 到達ルートがあるか探索し、最初にめくるべき index を返す。
   * 「取れば21になる確定ルート」がある局面では、CPUがスタンドより優先して続行するために使う。
   */
  function cpuFindKnownTwentyOneFirstFlip(sessionKeys) {
    const knownIndices = faceDownSlotIndices().filter(function (idx) {
      return slots[idx].everRevealed;
    });
    if (!knownIndices.length) return null;

    const baseTotal = handTotal(sessionKeys, pictureMode, aceMode);
    if (baseTotal >= 21) return null;

    const MAX_DEPTH = Math.min(8, knownIndices.length);
    const NODE_LIMIT = 12000;
    let visited = 0;

    function scoreTo21(idx, currentTotal) {
      const nextTotal = handTotal(
        sessionKeys.concat([slots[idx].key]),
        pictureMode,
        aceMode
      );
      return Math.abs(21 - nextTotal) + (nextTotal > 21 ? 1000 : 0);
    }

    function dfs(currKeys, remain, firstIdx, depth) {
      visited++;
      if (visited > NODE_LIMIT) return null;

      const t = handTotal(currKeys, pictureMode, aceMode);
      if (t === 21) return firstIdx;
      if (t > 21 || depth >= MAX_DEPTH) return null;

      const ranked = remain.slice().sort(function (a, b) {
        return scoreTo21(a, t) - scoreTo21(b, t);
      });

      for (let i = 0; i < ranked.length; i++) {
        const idx = ranked[i];
        const nextFirst = firstIdx === null ? idx : firstIdx;
        const nextRemain = remain.filter(function (x) {
          return x !== idx;
        });
        const got = dfs(
          currKeys.concat([slots[idx].key]),
          nextRemain,
          nextFirst,
          depth + 1
        );
        if (got !== null) return got;
      }
      return null;
    }

    return dfs(sessionKeys.slice(), knownIndices, null, 0);
  }

  // 未知カードの期待値を安定化させるため、低得点～高得点を均等に拾う層化サンプル。
  function samplePoolKeysForExpectation(pool) {
    if (pool.length <= CPU_MAX_POOL_ENUMERATE) return pool.slice();
    const sorted = pool.slice().sort(function (a, b) {
      return singleCardPileScore(a) - singleCardPileScore(b);
    });
    const out = [];
    const n = sorted.length;
    for (let i = 0; i < CPU_MAX_POOL_SAMPLES; i++) {
      const pos = Math.floor((i * (n - 1)) / Math.max(1, CPU_MAX_POOL_SAMPLES - 1));
      out.push(sorted[pos]);
    }
    return out;
  }

  /** @param {string} key */
  function rankNum(key) {
    return parseInt(key.slice(1), 10);
  }

  /**
   * @param {string[]} keys
   * @param {string} pictureMode 'ten' | 'rank'
   * @param {string} aceMode 'soft' | 'one'
   */
  function handTotal(keys, pictureMode, aceMode) {
    let sum = 0;
    let acesAsEleven = 0;
    for (const k of keys) {
      const n = rankNum(k);
      if (n === 1) {
        if (aceMode === "one") {
          sum += 1;
        } else {
          sum += 11;
          acesAsEleven++;
        }
      } else if (n >= 11) {
        sum += pictureMode === "ten" ? 10 : n;
      } else {
        sum += n;
      }
    }
    if (aceMode === "soft") {
      while (sum > 21 && acesAsEleven > 0) {
        sum -= 10;
        acesAsEleven--;
      }
    }
    return sum;
  }

  /**
   * @param {string[]} keys
   */
  function pileScoreFromKeys(keys, pictureMode, aceMode) {
    let s = 0;
    for (const k of keys) {
      const n = rankNum(k);
      if (n === 1) {
        s += aceMode === "one" ? 1 : 11;
      } else if (n >= 11) {
        s += pictureMode === "ten" ? 10 : n;
      } else {
        s += n;
      }
    }
    return s;
  }

  const elSetup = document.getElementById("setup");
  const elPlay = document.getElementById("playArea");
  const btnStart = document.getElementById("btnStart");
  const btnStand = document.getElementById("btnStand");
  const chkStandShuffle = document.getElementById("chkStandShuffle");
  const elShuffleLabelText = document.getElementById("shuffleLabelText");
  const btnOutcomeOk = document.getElementById("btnOutcomeOk");
  const btnNewGame = document.getElementById("btnNewGame");
  const elGrid = document.getElementById("grid");
  const elAxisTop = document.getElementById("axisTop");
  const elAxisLeft = document.getElementById("axisLeft");
  const elTurn = document.getElementById("turnLabel");
  const elSession = document.getElementById("sessionSum");
  const elMsg = document.getElementById("message");
  const elPlayers = document.getElementById("playersList");
  const cpuCheckbox = document.getElementById("cpuOpponent");

  let playerCount = 2;
  /** @type {'cards'|'score'} */
  let winMode = "cards";
  /** @type {'ten'|'rank'} */
  let pictureMode = "ten";
  /** @type {'soft'|'one'} */
  let aceMode = "soft";
  /** バスト時処理（デフォルト: バスト札のみ戻し）: 全戻し / バスト札のみ戻し */
  /** @type {'allBack'|'lastBack'} */
  let bustMode = "lastBack";
  let cpuEnabled = false;
  /** CPUがプレイヤー配列のこの index（2人CPU対戦時は 1） */
  let cpuPlayerIndex = 1;

  /** @type {{ name: string, collectedKeys: string[], isCpu?: boolean }[]} */
  let players = [];
  /** @type {{ key: string, flipped: boolean, removed: boolean, everRevealed: boolean }[]} */
  let slots = [];
  let currentPlayer = 0;
  /** @type {number[]} indices in slots */
  let sessionIndices = [];
  /** @type {'idle'|'decide'|'outcomeReveal'} */
  let phase = "idle";
  /** @type {'bust'|'twentyone'|null} */
  let outcomeKind = null;
  let interactionLocked = false;
  let cpuScheduleTimer = null;
  let cpuThinkDeadlineMs = 0;
  /** CPUのバスト／21／取得時に表札を確認できる待ち（ミリ秒）。スタート時に設定から読込 */
  let cpuRevealDelayMs = 3000;
  /** 後攻プレイヤーが1ゲーム中に使える終了時シャッフル回数 */
  let secondShuffleLimit = 2;
  let secondShuffleLeft = 2;
  /** そのゲームで実際に後攻になったプレイヤー index */
  let secondPlayerIndex = 1;

  function readCpuRevealDelayMs() {
    const el = document.getElementById("cpuRevealSec");
    if (!el) {
      cpuRevealDelayMs = 3000;
      return;
    }
    const v = parseFloat(el.value, 10);
    if (isNaN(v)) {
      cpuRevealDelayMs = 3000;
      return;
    }
    cpuRevealDelayMs = Math.min(30000, Math.max(500, Math.round(v * 1000)));
  }

  /** CPU対戦チェック時と同じセットアップ状態を復元（新しいゲーム後など） */
  function applyCpuSetupUiState() {
    playerCount = 2;
    btnStart.disabled = false;
  }

  function readSecondShuffleLimit() {
    const el = document.getElementById("secondShuffleCount");
    if (!el) {
      secondShuffleLimit = 2;
      return;
    }
    const n = parseInt(el.value, 10);
    if (isNaN(n)) {
      secondShuffleLimit = 2;
      return;
    }
    secondShuffleLimit = Math.min(20, Math.max(0, n));
  }

  function refreshCpuExtraSetupVisibility() {
    const show = !!(cpuCheckbox && cpuCheckbox.checked);
    const delay = document.getElementById("cpuDelayWrap");
    const first = document.getElementById("cpuFirstWrap");
    if (delay) delay.classList.toggle("hidden", !show);
    if (first) first.classList.toggle("hidden", !show);
  }

  // 開始前UIの選択値（勝敗条件・札評価・バスト処理など）をゲーム内状態へ反映する。
  function readSetupOptions() {
    const winEl = document.querySelector('input[name="winMode"]:checked');
    const picEl = document.querySelector('input[name="pictureMode"]:checked');
    const aceEl = document.querySelector('input[name="aceMode"]:checked');
    const bustEl = document.querySelector('input[name="bustMode"]:checked');
    winMode = winEl && winEl.value === "score" ? "score" : "cards";
    pictureMode = picEl && picEl.value === "rank" ? "rank" : "ten";
    aceMode = aceEl && aceEl.value === "one" ? "one" : "soft";
    bustMode = bustEl && bustEl.value === "lastBack" ? "lastBack" : "allBack";
    cpuEnabled = !!(cpuCheckbox && cpuCheckbox.checked);
    if (cpuEnabled) {
      playerCount = 2;
    }
    readCpuRevealDelayMs();
    readSecondShuffleLimit();
  }

  function isCpuTurn() {
    return (
      cpuEnabled &&
      players[currentPlayer] &&
      players[currentPlayer].isCpu === true
    );
  }

  function refreshCpuPlayClass() {
    elPlay.classList.toggle(
      "play--cpu-active",
      cpuEnabled && isCpuTurn()
    );
  }

  function canUseSecondEndShuffleNow() {
    return (
      currentPlayer === secondPlayerIndex &&
      phase === "decide" &&
      sessionIndices.length > 0 &&
      secondShuffleLeft > 0
    );
  }

  function canUseSecondBustShuffleNow() {
    return (
      currentPlayer === secondPlayerIndex &&
      phase === "outcomeReveal" &&
      outcomeKind === "bust" &&
      secondShuffleLeft > 0
    );
  }

  function shouldApplyShuffleByCheckbox() {
    return !!(chkStandShuffle && chkStandShuffle.checked);
  }

  function countKnownFaceDownCards() {
    let n = 0;
    for (let i = 0; i < slots.length; i++) {
      if (slots[i].removed) continue;
      if (!slots[i].flipped && slots[i].everRevealed) n++;
    }
    return n;
  }

  function shouldCpuUseSecondShuffleOnStand() {
    return currentPlayer === secondPlayerIndex && secondShuffleLeft > 0 && countKnownFaceDownCards() > 0;
  }

  function shouldCpuUseSecondShuffleOnBust() {
    return currentPlayer === secondPlayerIndex && secondShuffleLeft > 0;
  }

  // 1ターンの思考時間制限チェック。
  function cpuTimeExceeded() {
    return cpuThinkDeadlineMs > 0 && Date.now() >= cpuThinkDeadlineMs;
  }

  function imgUrl(key) {
    return IMG_DIR + key + ".png";
  }

  function backUrl() {
    return IMG_DIR + "back.png";
  }

  function faceDownOnFieldCount() {
    let n = 0;
    for (let i = 0; i < slots.length; i++) {
      if (slots[i].removed) continue;
      if (!slots[i].flipped) n++;
    }
    return n;
  }

  /** 場に伏せて残っているスロット index */
  function faceDownSlotIndices() {
    const a = [];
    for (let i = 0; i < slots.length; i++) {
      if (slots[i].removed) continue;
      if (!slots[i].flipped) a.push(i);
    }
    return a;
  }

  /**
   * まだ一度も表向きになっていない伏せの位置に割り当てられるカードの multiset（取得済み・
   * 場で表向き・一度でも見えた伏せの実体は除く）
   */
  function buildRemainingUnknownPool() {
    const used = Object.create(null);
    for (let p = 0; p < players.length; p++) {
      const ck = players[p].collectedKeys;
      for (let i = 0; i < ck.length; i++) used[ck[i]] = true;
    }
    for (let i = 0; i < slots.length; i++) {
      if (slots[i].removed) continue;
      if (slots[i].flipped) used[slots[i].key] = true;
      else if (slots[i].everRevealed) used[slots[i].key] = true;
    }
    const pool = [];
    const deck = buildDeck();
    for (let i = 0; i < deck.length; i++) {
      if (!used[deck[i]]) pool.push(deck[i]);
    }
    return pool;
  }

  /** 伏せ札1枚の勝敗用ポイント（数字の合計モードの集計と整合） */
  function singleCardPileScore(key) {
    return pileScoreFromKeys([key], pictureMode, aceMode);
  }

  function playerStatForMode(playerIndex) {
    if (winMode === "cards") {
      return players[playerIndex].collectedKeys.length;
    }
    return pileScoreFromKeys(players[playerIndex].collectedKeys, pictureMode, aceMode);
  }

  /**
   * 相手の次ターン1手（最初の1枚）で期待できる最大獲得量を近似する。
   * ここでは「最初の1枚をめくって安全に終了」を下限ベースに評価する。
   */
  function cpuEstimateOpponentOneTurnGain(poolV) {
    const indices = faceDownSlotIndices();
    if (!indices.length) return 0;

    let best = 0;
    for (let i = 0; i < indices.length; i++) {
      const idx = indices[i];
      const s = slots[idx];
      let ev = 0;
      if (s.everRevealed) {
        ev = singleCardPileScore(s.key);
      } else if (poolV.length > 0) {
        let sum = 0;
        for (let k = 0; k < poolV.length; k++) {
          sum += singleCardPileScore(poolV[k]);
        }
        ev = sum / poolV.length;
      }
      if (ev > best) best = ev;
    }
    return best;
  }

  /**
   * 点差と残り札から、CPUがどれだけ攻めるべきかを返す。
   * +: 攻め寄り（続行しやすい） / -: 守り寄り（スタンドしやすい）
   */
  function cpuAggressionFromLead(lead, remainCount) {
    const late = remainCount <= 18 ? 1.15 : 1.0;
    if (lead <= -15) return 240 * late;
    if (lead <= -8) return 140 * late;
    if (lead < 0) return 70 * late;
    if (lead >= 15) return -170 * late;
    if (lead >= 8) return -100 * late;
    if (lead > 0) return -45 * late;
    return 0;
  }

  /** 未開示プール + 一度見えた伏せの確定分数の合計（評価用） */
  function cpuRemainingPotentialFromPool(poolV) {
    let s = 0;
    for (let i = 0; i < poolV.length; i++) {
      s += singleCardPileScore(poolV[i]);
    }
    for (let i = 0; i < slots.length; i++) {
      if (slots[i].removed) continue;
      if (!slots[i].flipped && slots[i].everRevealed) {
        s += singleCardPileScore(slots[i].key);
      }
    }
    return s;
  }

  /**
   * @param {string[]} sessionKeys
   * @param {string[]} poolV 未開示伏せに残るカード multiset（再帰時は仮想プール）
   */
  function cpuUtilityIfStandNow(sessionKeys, poolV) {
    if (!sessionKeys.length) return -1e18;
    const human = 0;
    const cpu = cpuPlayerIndex;
    const gain = pileScoreFromKeys(sessionKeys, pictureMode, aceMode);
    const nGain = sessionKeys.length;

    const myStat = playerStatForMode(cpu) + (winMode === "cards" ? nGain : gain);
    const oppStat = playerStatForMode(human);

    const remSum = cpuRemainingPotentialFromPool(poolV);
    const lead = myStat - oppStat;
    const oppOneTurnGain = cpuEstimateOpponentOneTurnGain(poolV);
    return lead * 1000 - oppOneTurnGain * 170 + remSum * 0.12 + nGain * 0.4;
  }

  /**
   * @param {string[]} poolV 現在の未開示 multiset（sessionKeys は場で表向きとしてグローバルと整合）
   */
  function cpuMaxValueThisTurnImperfect(sessionKeys, poolV, depth) {
    if (cpuTimeExceeded()) {
      return cpuUtilityIfStandNow(sessionKeys, poolV);
    }
    const t = handTotal(sessionKeys, pictureMode, aceMode);
    if (t > 21) return -1e18;
    if (t === 21) return 1e15 + sessionKeys.length;

    const standU = cpuUtilityIfStandNow(sessionKeys, poolV);
    if (depth <= 0) return standU;

    const indices = buildCpuCandidateIndices(faceDownSlotIndices());
    if (indices.length === 0) return standU;

    let best = standU;
    for (let x = 0; x < indices.length; x++) {
      if (cpuTimeExceeded()) break;
      const idx = indices[x];
      const v = cpuMarginalFlipValue(idx, sessionKeys, poolV, depth);
      best = Math.max(best, v);
    }
    return best;
  }

  /**
   * 1スロットめくりの周辺期待値（未開示スロットは pool 上で一様に周辺化）
   */
  function cpuMarginalFlipValue(idx, sessionKeys, poolV, depth) {
    if (cpuTimeExceeded()) {
      return cpuUtilityIfStandNow(sessionKeys, poolV);
    }
    const slot = slots[idx];
    if (slot.everRevealed && !slot.flipped) {
      const k = slot.key;
      const nextKeys = sessionKeys.concat([k]);
      const nt = handTotal(nextKeys, pictureMode, aceMode);
      if (nt > 21) return -1e18;
      if (nt === 21) return 1e15 + nextKeys.length;
      return cpuMaxValueThisTurnImperfect(nextKeys, poolV, depth - 1);
    }

    const pool = poolV;
    if (!pool.length) return -1e18;

    const sampleKeys = samplePoolKeysForExpectation(pool);

    let sum = 0;
    let cnt = 0;
    for (let pi = 0; pi < sampleKeys.length; pi++) {
      if (cpuTimeExceeded()) break;
      const k = sampleKeys[pi];
      const newPool = removeOneKeyFromPool(pool, k);
      const nextKeys = sessionKeys.concat([k]);
      const nt = handTotal(nextKeys, pictureMode, aceMode);
      if (nt > 21) {
        sum += -1e18;
      } else if (nt === 21) {
        sum += 1e15 + nextKeys.length;
      } else {
        sum += cpuMaxValueThisTurnImperfect(nextKeys, newPool, depth - 1);
      }
      cnt++;
    }
    return sum / Math.max(1, cnt);
  }

  /**
   * 最適行動: 取得して終了(通常/シャッフル) vs 次にめくるスロット
   * @returns {{ stand: true, useShuffle?: boolean } | { flip: number }}
   */
  // 現在ターンで「続行」と「取得終了」のどちらが有利かを比較して行動を返す。
  function cpuChooseStandOrFlip() {
    cpuThinkDeadlineMs = Date.now() + CPU_THINK_BUDGET_MS;
    const sessionKeys = sessionIndices.map((i) => slots[i].key);
    const indicesAll = faceDownSlotIndices();
    const pool = buildRemainingUnknownPool();

    if (indicesAll.length === 0) {
      return { stand: true, useShuffle: shouldCpuUseSecondShuffleOnStand() };
    }

    const indices = buildCpuCandidateIndices(indicesAll);
    const depth = cpuDepthForState(indices.length);

    // 続行中に「確定札だけで21到達」が見えるなら、スタンドせずそのルートを最優先する。
    if (sessionKeys.length > 0) {
      const forced21Idx = cpuFindKnownTwentyOneFirstFlip(sessionKeys);
      if (forced21Idx !== null) {
        return { flip: forced21Idx };
      }

    }

    if (sessionKeys.length === 0) {
      let bestIdx = -1;
      let bestVal = -Infinity;
      for (let x = 0; x < indices.length; x++) {
        if (cpuTimeExceeded()) break;
        const idx = indices[x];
        const v = cpuMarginalFlipValue(idx, [], pool, depth);
        if (v > bestVal) {
          bestVal = v;
          bestIdx = idx;
        }
      }
      if (bestIdx < 0) {
        return { flip: indicesAll[0] };
      }
      return { flip: bestIdx };
    }

    const standU = cpuUtilityIfStandNow(sessionKeys, pool);
    const cpu = cpuPlayerIndex;
    const human = 0;
    const leadNow = playerStatForMode(cpu) - playerStatForMode(human);
    const aggressionBias = cpuAggressionFromLead(leadNow, indicesAll.length);
    let bestFlip = null;
    let bestVal = -Infinity;
    for (let x = 0; x < indices.length; x++) {
      if (cpuTimeExceeded()) break;
      const idx = indices[x];
      const v = cpuMarginalFlipValue(idx, sessionKeys, pool, depth);
      if (v > bestVal) {
        bestVal = v;
        bestFlip = idx;
      }
    }

    if (bestFlip === null) {
      return { stand: true, useShuffle: shouldCpuUseSecondShuffleOnStand() };
    }
    if (standU >= bestVal + aggressionBias) {
      return { stand: true, useShuffle: shouldCpuUseSecondShuffleOnStand() };
    }
    return { flip: bestFlip };
  }

  function clearCpuSchedule() {
    if (cpuScheduleTimer !== null) {
      window.clearTimeout(cpuScheduleTimer);
      cpuScheduleTimer = null;
    }
  }

  function scheduleCpuTurn() {
    clearCpuSchedule();
    if (!cpuEnabled || !isCpuTurn()) return;
    if (phase === "outcomeReveal") return;
    if (interactionLocked) return;
    cpuScheduleTimer = window.setTimeout(function () {
      cpuScheduleTimer = null;
      runCpuStep();
    }, 420);
  }

  // CPUの1手実行。setTimeout / rAF で分割してUIフリーズを避ける。
  function runCpuStep() {
    if (!cpuEnabled || !isCpuTurn()) return;
    if (interactionLocked) {
      scheduleCpuTurn();
      return;
    }
    if (phase === "outcomeReveal") return;
    if (phase !== "idle" && phase !== "decide") return;

    setMessage("CPU思考中…");

    window.setTimeout(function () {
      if (!cpuEnabled || !isCpuTurn()) return;
      if (interactionLocked) return;
      if (phase === "outcomeReveal") return;
      if (phase !== "idle" && phase !== "decide") return;

      const runAi = function () {
        if (!cpuEnabled || !isCpuTurn()) return;
        if (interactionLocked) return;
        if (phase === "outcomeReveal") return;
        if (phase !== "idle" && phase !== "decide") return;

        const decision = cpuChooseStandOrFlip();
        cpuThinkDeadlineMs = 0;
        if (decision.stand) {
          executeStandAndAdvance(!!decision.useShuffle);
        } else {
          applyFlip(decision.flip);
          if (
            phase === "decide" &&
            isCpuTurn() &&
            !interactionLocked
          ) {
            window.setTimeout(runCpuStep, 520);
          }
        }
      };

      if (typeof window.requestAnimationFrame === "function") {
        window.requestAnimationFrame(function () {
          window.setTimeout(runAi, 0);
        });
      } else {
        window.setTimeout(runAi, 0);
      }
    }, 280);
  }

  function setMessage(text) {
    elMsg.textContent = text;
  }

  function setNewGameVisible(show) {
    if (show) {
      btnNewGame.classList.remove("hidden");
      btnNewGame.setAttribute("aria-hidden", "false");
    } else {
      btnNewGame.classList.add("hidden");
      btnNewGame.setAttribute("aria-hidden", "true");
    }
  }

  function renderPlayers() {
    elPlayers.innerHTML = "";
    players.forEach((p, i) => {
      const row = document.createElement("div");
      row.className = "player-row" + (i === currentPlayer ? " current" : "");
      const scorePart =
        winMode === "score"
          ? "・" +
            pileScoreFromKeys(p.collectedKeys, pictureMode, aceMode) +
            " 点"
          : "";
      row.innerHTML =
        '<span class="player-name">' +
        escapeHtml(p.name) +
        '</span><span class="player-score">取得 ' +
        p.collectedKeys.length +
        " 枚" +
        scorePart +
        "</span>";
      elPlayers.appendChild(row);
    });
  }

  function escapeHtml(s) {
    return s
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;")
      .replace(/"/g, "&quot;");
  }

  function updateTurnUI() {
    elTurn.textContent = players[currentPlayer].name + " のターン";
    renderPlayers();
    updateSessionUI();
    refreshCpuPlayClass();
    scheduleCpuTurn();
  }

  function currentHandTotal() {
    const keys = sessionIndices.map((i) => slots[i].key);
    return keys.length ? handTotal(keys, pictureMode, aceMode) : 0;
  }

  // めくり中手札の合計表示と、操作ボタンの有効状態を更新。
  function updateSessionUI() {
    const keys = sessionIndices.map((i) => slots[i].key);
    const total = keys.length ? handTotal(keys, pictureMode, aceMode) : 0;
    if (keys.length === 0) {
      elSession.innerHTML = "めくった札: なし";
    } else {
      elSession.innerHTML =
        'めくった札の合計: <strong>' +
        total +
        "</strong>" +
        ' <span class="session-cards">' +
        escapeHtml(keys.join(" ")) +
        "</span>";
    }

    const canShuffleOnStand = canUseSecondEndShuffleNow();
    const canShuffleOnBust = canUseSecondBustShuffleNow();
    const canShuffleNow = canShuffleOnStand || canShuffleOnBust;

    if (isCpuTurn()) {
      btnStand.disabled = true;
    } else if (phase === "decide") {
      btnStand.disabled = sessionIndices.length === 0;
    } else if (phase === "outcomeReveal" && outcomeKind === "bust") {
      btnStand.disabled = true;
    } else {
      btnStand.disabled = true;
    }

    if (chkStandShuffle) {
      chkStandShuffle.disabled = !canShuffleNow;
      if (!canShuffleNow) chkStandShuffle.checked = false;
    }
    if (elShuffleLabelText) {
      elShuffleLabelText.textContent = "シャッフル（残 " + secondShuffleLeft + " 回）";
    }
  }

  function columnLabel(n) {
    let x = n;
    let label = "";
    while (x > 0) {
      const rem = (x - 1) % 26;
      label = String.fromCharCode(97 + rem) + label;
      x = Math.floor((x - 1) / 26);
    }
    return label;
  }

  function renderBoardAxisLabels(totalCards) {
    if (!elAxisTop || !elAxisLeft) return;
    const rows = BOARD_ROWS;
    const top = [];
    const left = [];
    for (let c = 1; c <= BOARD_COLS; c++) {
      top.push("<span>" + columnLabel(c) + "</span>");
    }
    for (let r = 1; r <= rows; r++) {
      left.push("<span>" + r + "</span>");
    }
    elAxisTop.style.gridTemplateColumns = "repeat(" + BOARD_COLS + ", var(--card-w))";
    elAxisLeft.style.gridTemplateRows = "repeat(" + rows + ", var(--card-h))";
    elAxisTop.innerHTML = top.join("");
    elAxisLeft.innerHTML = left.join("");
  }

  function createGrid() {
    elGrid.innerHTML = "";
    elGrid.style.gridTemplateColumns = "repeat(" + BOARD_COLS + ", var(--card-w))";
    renderBoardAxisLabels(slots.length);
    slots.forEach((slot, index) => {
      const wrap = document.createElement("div");
      wrap.className = "slot";
      wrap.dataset.index = String(index);
      if (slot.removed) wrap.classList.add("removed");
      if (slot.flipped) wrap.classList.add("flipped");

      const inner = document.createElement("div");
      inner.className = "slot-inner";

      const back = document.createElement("div");
      back.className = "face back";
      const ib = document.createElement("img");
      ib.src = backUrl();
      ib.alt = "裏面";
      ib.loading = "lazy";
      back.appendChild(ib);

      const front = document.createElement("div");
      front.className = "face front";
      const ifr = document.createElement("img");
      ifr.src = imgUrl(slot.key);
      ifr.alt = slot.key;
      ifr.loading = "lazy";
      front.appendChild(ifr);

      inner.appendChild(back);
      inner.appendChild(front);
      wrap.appendChild(inner);

      wrap.addEventListener("click", () => onSlotClick(index));
      elGrid.appendChild(wrap);
    });
  }

  function syncSlotDOM(index) {
    const wrap = elGrid.querySelector('.slot[data-index="' + index + '"]');
    if (!wrap) return;
    const s = slots[index];
    wrap.classList.toggle("flipped", s.flipped);
    wrap.classList.toggle("removed", s.removed);
  }

  // シャッフル直後に「中央へ寄せてから再配置された」見た目を付ける。
  function playShuffleRedealAnimation() {
    if (!elGrid) return;
    const nodes = Array.prototype.slice.call(elGrid.querySelectorAll(".slot"));
    if (!nodes.length) return;

    const gridRect = elGrid.getBoundingClientRect();
    const cx = gridRect.left + gridRect.width / 2;
    const cy = gridRect.top + gridRect.height / 2;

    nodes.forEach(function (node) {
      const r = node.getBoundingClientRect();
      const sx = r.left + r.width / 2;
      const sy = r.top + r.height / 2;
      const dx = cx - sx;
      const dy = cy - sy;
      node.style.setProperty("--shuffle-dx", dx.toFixed(1) + "px");
      node.style.setProperty("--shuffle-dy", dy.toFixed(1) + "px");
    });

    elGrid.classList.add("shuffle-redeal");
    // 1フレーム待ってから active を付け、中央→再配置の遷移を確実に発火させる
    const start = function () {
      elGrid.classList.add("shuffle-redeal-active");
    };
    if (typeof window.requestAnimationFrame === "function") {
      window.requestAnimationFrame(function () {
        window.requestAnimationFrame(start);
      });
    } else {
      window.setTimeout(start, 16);
    }

    window.setTimeout(function () {
      elGrid.classList.remove("shuffle-redeal");
      elGrid.classList.remove("shuffle-redeal-active");
      nodes.forEach(function (node) {
        node.style.removeProperty("--shuffle-dx");
        node.style.removeProperty("--shuffle-dy");
      });
    }, SHUFFLE_REDEAL_MS + 40);
  }

  function hintDecideMessage() {
    if (faceDownOnFieldCount() > 0) {
      return isCpuTurn()
        ? "CPUのターンです。"
        : "伏せ札を追加でめくるか、ターン終了を選んでください。";
    }
    return "伏せ札がありません。ターン終了してください。";
  }

  /**
   * @returns {boolean} バストまたは21で収束したら true
   */
  // 1枚めくって状態遷移（通常継続 / 21 / バスト）を判定。
  function applyFlip(index) {
    const s = slots[index];
    if (s.removed || s.flipped) return false;

    s.everRevealed = true;
    s.flipped = true;
    sessionIndices.push(index);
    syncSlotDOM(index);

    const keys = sessionIndices.map((i) => slots[i].key);
    const total = handTotal(keys, pictureMode, aceMode);

    if (total > 21) {
      beginOutcomeBust();
      return true;
    }
    if (total === 21) {
      beginOutcomeTwentyOne();
      return true;
    }

    phase = "decide";
    setMessage(hintDecideMessage());
    updateSessionUI();
    refreshCpuPlayClass();
    return false;
  }

  function onSlotClick(index) {
    if (interactionLocked) return;
    if (cpuEnabled && isCpuTurn()) return;
    if (phase === "outcomeReveal") return;
    if (phase !== "idle" && phase !== "decide") return;
    const s = slots[index];
    if (s.removed || s.flipped) return;

    applyFlip(index);
  }

  function beginOutcomeBust() {
    phase = "outcomeReveal";
    outcomeKind = "bust";
    btnStand.disabled = true;
    btnOutcomeOk.classList.remove("hidden");
    const t = currentHandTotal();
    setMessage("バスト（合計 " + t + "）。確認完了を押してください。");
    updateSessionUI();
    refreshCpuPlayClass();
    if (isCpuTurn()) {
      window.setTimeout(function () {
        confirmOutcome(shouldCpuUseSecondShuffleOnBust());
      }, cpuRevealDelayMs);
    }
  }

  function beginOutcomeTwentyOne() {
    phase = "outcomeReveal";
    outcomeKind = "twentyone";
    btnStand.disabled = true;
    btnOutcomeOk.classList.remove("hidden");
    const n = sessionIndices.length;
    setMessage("合計21（" + n + "枚）。確認完了で取得します。");
    updateSessionUI();
    refreshCpuPlayClass();
    if (isCpuTurn()) {
      window.setTimeout(function () {
        confirmOutcome();
      }, cpuRevealDelayMs);
    }
  }

  // 「確認完了」後の共通確定処理（バスト時は設定ルールに従って処理、21時は全取得）。
  function confirmOutcome(useSecondShuffleOnBust) {
    if (phase !== "outcomeReveal") return;
    if (outcomeKind === "bust") {
      const withShuffle = !!useSecondShuffleOnBust && canUseSecondBustShuffleNow();
      const toReset = sessionIndices.slice();
      sessionIndices = [];
      outcomeKind = null;
      phase = "idle";
      btnOutcomeOk.classList.add("hidden");
      if (bustMode === "lastBack" && toReset.length > 1) {
        const bustIdx = toReset[toReset.length - 1];
        const keepIdxs = toReset.slice(0, -1);
        slots[bustIdx].flipped = false;
        syncSlotDOM(bustIdx);
        keepIdxs.forEach(function (idx) {
          players[currentPlayer].collectedKeys.push(slots[idx].key);
          slots[idx].removed = true;
          slots[idx].flipped = false;
          syncSlotDOM(idx);
        });
        renderPlayers();
        if (withShuffle) {
          secondShuffleLeft--;
          reshuffleBoardCards();
        }
      } else if (withShuffle) {
        secondShuffleLeft--;
        reshuffleBoardCards();
      } else {
        toReset.forEach(function (idx) {
          slots[idx].flipped = false;
          syncSlotDOM(idx);
        });
      }
      nextPlayer();
      return;
    }
    if (outcomeKind === "twentyone") {
      const idxs = sessionIndices.slice();
      idxs.forEach(function (idx) {
        players[currentPlayer].collectedKeys.push(slots[idx].key);
        slots[idx].removed = true;
        slots[idx].flipped = false;
        syncSlotDOM(idx);
      });
      sessionIndices = [];
      outcomeKind = null;
      phase = "idle";
      btnOutcomeOk.classList.add("hidden");
      renderPlayers();
      updateSessionUI();
      refreshCpuPlayClass();
      if (isGameOver()) {
        endGame();
        return;
      }
      if (isCpuTurn()) {
        setMessage("CPUが取得。CPUターン継続。");
        scheduleCpuTurn();
      } else {
        setMessage("取得完了。あなたの追加ターンです。");
      }
    }
  }

  // 「ターン終了」処理の入口。CPU時は確認待ち時間を挟む。
  function executeStandAndAdvance(useSecondShuffle) {
    if (phase !== "decide" || sessionIndices.length === 0) return;
    const took = sessionIndices.length;

    if (cpuEnabled && isCpuTurn() && cpuRevealDelayMs > 0) {
      interactionLocked = true;
      btnStand.disabled = true;
      const secDisp = (cpuRevealDelayMs / 1000).toFixed(1).replace(/\.0$/, "");
      setMessage("CPUが " + took + " 枚取得して終了。待機中（約 " + secDisp + " 秒）…");
      window.setTimeout(function () {
        if (phase !== "decide" || sessionIndices.length === 0) return;
        executeStandAndAdvanceApply(took, useSecondShuffle);
      }, cpuRevealDelayMs);
      return;
    }

    executeStandAndAdvanceApply(took, useSecondShuffle);
  }

  function executeStandAndAdvanceApply(took, useSecondShuffle) {
    interactionLocked = true;
    phase = "idle";
    btnStand.disabled = true;
    if (chkStandShuffle) chkStandShuffle.disabled = true;

    sessionIndices.forEach(function (idx) {
      players[currentPlayer].collectedKeys.push(slots[idx].key);
      slots[idx].removed = true;
      slots[idx].flipped = false;
      syncSlotDOM(idx);
    });
    sessionIndices = [];

    if (useSecondShuffle && currentPlayer === 1 && secondShuffleLeft > 0) {
      secondShuffleLeft--;
      reshuffleBoardCards();
    }

    setMessage(players[currentPlayer].name + "が " + took + " 枚取得して終了。" + (useSecondShuffle ? " 盤面をシャッフルしました。" : ""));

    renderPlayers();
    updateSessionUI();

    if (isGameOver()) {
      interactionLocked = false;
      endGame();
      return;
    }

    window.setTimeout(function () {
      interactionLocked = false;
      nextPlayer();
    }, 450);
  }

  function standAndTake() {
    if (cpuEnabled && isCpuTurn()) return;
    if (phase !== "decide" || sessionIndices.length === 0) return;
    executeStandAndAdvance(canUseSecondEndShuffleNow() && shouldApplyShuffleByCheckbox());
  }

  function reshuffleBoardCards() {
    const activeIndices = [];
    const activeKeys = [];
    for (let i = 0; i < slots.length; i++) {
      if (slots[i].removed) continue;
      activeIndices.push(i);
      activeKeys.push(slots[i].key);
    }
    const shuffledKeys = shuffle(activeKeys);
    for (let x = 0; x < activeIndices.length; x++) {
      const idx = activeIndices[x];
      slots[idx].key = shuffledKeys[x];
      slots[idx].flipped = false;
      slots[idx].everRevealed = false;
      syncSlotDOM(idx);
    }
    createGrid();
    playShuffleRedealAnimation();
  }

  function isGameOver() {
    return slots.every(function (s) {
      return s.removed;
    });
  }

  function endGame() {
    clearCpuSchedule();
    phase = "idle";
    outcomeKind = null;
    btnStand.disabled = true;
    if (chkStandShuffle) chkStandShuffle.disabled = true;
    btnOutcomeOk.classList.add("hidden");
    let best = -1;
    const winners = [];
    players.forEach(function (p, i) {
      const stat =
        winMode === "cards"
          ? p.collectedKeys.length
          : pileScoreFromKeys(p.collectedKeys, pictureMode, aceMode);
      if (stat > best) {
        best = stat;
        winners.length = 0;
        winners.push(i);
      } else if (stat === best) {
        winners.push(i);
      }
    });
    if (winners.length > 1) {
      // 同点は後攻勝ち
      winners.length = 0;
      winners.push(secondPlayerIndex);
    }
    const names = winners.map(function (i) {
      return players[i].name;
    }).join("、");
    const unit = winMode === "cards" ? "枚" : "点";
    setMessage("ゲーム終了！ 勝者: " + names + "（" + best + " " + unit + "）");
    elTurn.textContent = "終了";
    renderPlayers();
    refreshCpuPlayClass();
    setNewGameVisible(true);
  }

  function nextPlayer() {
    if (isGameOver()) {
      endGame();
      return;
    }
    currentPlayer = (currentPlayer + 1) % playerCount;
    phase = "idle";
    sessionIndices = [];
    outcomeKind = null;
    btnOutcomeOk.classList.add("hidden");
    setMessage("場から札をめくってください。");
    updateTurnUI();
  }

  // 1ゲーム分の状態を初期化し、先攻選択に従って開始する。
  function startGame() {
    readSetupOptions();
    clearCpuSchedule();
    const deck = shuffle(buildDeck());
    slots = deck.map(function (key) {
      return {
        key: key,
        flipped: false,
        removed: false,
        everRevealed: false,
      };
    });
    players = [];
    if (cpuEnabled) {
      players.push({
        name: "あなた",
        collectedKeys: [],
        isCpu: false,
      });
      players.push({
        name: "CPU",
        collectedKeys: [],
        isCpu: true,
      });
      playerCount = 2;
      cpuPlayerIndex = 1;
    } else {
      for (let i = 0; i < playerCount; i++) {
        players.push({
          name: "プレイヤー " + (i + 1),
          collectedKeys: [],
        });
      }
      cpuPlayerIndex = 1;
    }
    if (cpuEnabled) {
      const firstEl = document.querySelector(
        'input[name="cpuFirst"]:checked'
      );
      const mode = firstEl ? firstEl.value : "human";
      if (mode === "random") {
        currentPlayer = Math.random() < 0.5 ? 0 : 1;
      } else if (mode === "cpu") {
        currentPlayer = 1;
      } else {
        currentPlayer = 0;
      }
    } else {
      currentPlayer = 0;
    }
    secondPlayerIndex = (currentPlayer + 1) % playerCount;
    sessionIndices = [];
    phase = "idle";
    outcomeKind = null;
    interactionLocked = false;
    secondShuffleLeft = secondShuffleLimit;

    elSetup.classList.add("hidden");
    elPlay.classList.remove("hidden");
    setNewGameVisible(false);
    btnOutcomeOk.classList.add("hidden");
    createGrid();
    if (cpuEnabled) {
      if (isCpuTurn()) {
        setMessage("CPUの先攻です。");
      } else {
        setMessage("あなたの先攻です。場から札をめくってください。");
      }
    } else {
      setMessage("場から札をめくってください。");
    }
    updateTurnUI();
    btnStand.disabled = true;
    if (chkStandShuffle) chkStandShuffle.disabled = true;
  }

  btnStand.addEventListener("click", standAndTake);
  btnOutcomeOk.addEventListener("click", function () {
    const useShuffle = canUseSecondBustShuffleNow() && shouldApplyShuffleByCheckbox();
    confirmOutcome(useShuffle);
  });

  btnNewGame.addEventListener("click", () => {
    clearCpuSchedule();
    setNewGameVisible(false);
    elPlay.classList.add("hidden");
    elSetup.classList.remove("hidden");
    btnOutcomeOk.classList.add("hidden");
    elGrid.innerHTML = "";
    elPlay.classList.remove("play--cpu-active");

    if (cpuCheckbox && cpuCheckbox.checked) {
      applyCpuSetupUiState();
    } else {
      playerCount = 2;
      btnStart.disabled = false;
    }
  });

  if (cpuCheckbox) {
    cpuCheckbox.addEventListener("change", function () {
      refreshCpuExtraSetupVisibility();
      if (cpuCheckbox.checked) {
        applyCpuSetupUiState();
      } else {
        playerCount = 2;
        btnStart.disabled = false;
      }
    });
    refreshCpuExtraSetupVisibility();
  }

  playerCount = 2;
  btnStart.disabled = false;

  btnStart.addEventListener("click", () => {
    readSetupOptions();
    playerCount = 2;
    startGame();
  });
})();
