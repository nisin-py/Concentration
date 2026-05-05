(function () {
  "use strict";

  const SUITS = ["d", "h", "k", "s"];
  const RANKS = [
    "01", "02", "03", "04", "05", "06", "07", "08", "09", "10", "11", "12", "13",
  ];
  const IMG_DIR = "playingcard_png/type-B/";
  /** CPUがターン内で読む先読み深さ（メインスレッド負荷とのバランス） */
  const CPU_SEARCH_DEPTH = 2;
  /** 未開示プールが大きいとき期待値をモンテカルロ近似するサンプル数（全組み合わせは数十秒ブロックするため） */
  const CPU_MAX_POOL_SAMPLES = 12;
  /** めくり候補スロットが多いとき評価する最大件数（ランダムサンプル） */
  const CPU_MAX_SLOT_BRANCH = 14;

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

  /** 候補が多すぎるとき評価コストを抑えるためのサンプル */
  function sampleSlotIndicesForCpu(indices) {
    if (indices.length <= CPU_MAX_SLOT_BRANCH) return indices;
    return shuffle(indices.slice()).slice(0, CPU_MAX_SLOT_BRANCH);
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

  function handRulesHint(pictureMode, aceMode) {
    const p =
      pictureMode === "ten" ? "絵札(J,Q,K)=10" : "絵札=11,12,13";
    const a = aceMode === "soft" ? "A=1/11最適" : "A=1";
    return "（" + p + "、" + a + "）";
  }

  const elSetup = document.getElementById("setup");
  const elPlay = document.getElementById("playArea");
  const btnStart = document.getElementById("btnStart");
  const btnStand = document.getElementById("btnStand");
  const btnOutcomeOk = document.getElementById("btnOutcomeOk");
  const btnNewGame = document.getElementById("btnNewGame");
  const elGrid = document.getElementById("grid");
  const elTurn = document.getElementById("turnLabel");
  const elSession = document.getElementById("sessionSum");
  const elMsg = document.getElementById("message");
  const elPlayers = document.getElementById("playersList");
  const cpuCheckbox = document.getElementById("cpuOpponent");
  const playerCountRow = document.getElementById("playerCountRow");

  let playerCount = 0;
  /** @type {'cards'|'score'} */
  let winMode = "cards";
  /** @type {'ten'|'rank'} */
  let pictureMode = "ten";
  /** @type {'soft'|'one'} */
  let aceMode = "soft";
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
  /** CPUのバスト／21／取得時に表札を確認できる待ち（ミリ秒）。スタート時に設定から読込 */
  let cpuRevealDelayMs = 3000;

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
    const row = playerCountRow;
    document.querySelectorAll(".setup-row .btn-ghost").forEach(function (b) {
      b.classList.remove("selected");
      if (b.getAttribute("data-players") === "2") {
        b.classList.add("selected");
      }
    });
    playerCount = 2;
    btnStart.disabled = false;
    if (row) {
      row.querySelectorAll("button").forEach(function (bt, i) {
        bt.disabled = i > 0;
      });
    }
  }

  function refreshCpuExtraSetupVisibility() {
    const show = !!(cpuCheckbox && cpuCheckbox.checked);
    const delay = document.getElementById("cpuDelayWrap");
    const first = document.getElementById("cpuFirstWrap");
    if (delay) delay.classList.toggle("hidden", !show);
    if (first) first.classList.toggle("hidden", !show);
  }

  function readSetupOptions() {
    const winEl = document.querySelector('input[name="winMode"]:checked');
    const picEl = document.querySelector('input[name="pictureMode"]:checked');
    const aceEl = document.querySelector('input[name="aceMode"]:checked');
    winMode = winEl && winEl.value === "score" ? "score" : "cards";
    pictureMode = picEl && picEl.value === "rank" ? "rank" : "ten";
    aceMode = aceEl && aceEl.value === "one" ? "one" : "soft";
    cpuEnabled = !!(cpuCheckbox && cpuCheckbox.checked);
    if (cpuEnabled) {
      playerCount = 2;
    }
    readCpuRevealDelayMs();
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

    const myStat =
      winMode === "cards"
        ? players[cpu].collectedKeys.length + nGain
        : pileScoreFromKeys(players[cpu].collectedKeys, pictureMode, aceMode) +
          gain;
    const oppStat =
      winMode === "cards"
        ? players[human].collectedKeys.length
        : pileScoreFromKeys(players[human].collectedKeys, pictureMode, aceMode);

    const remSum = cpuRemainingPotentialFromPool(poolV);
    const lead = myStat - oppStat;
    return lead * 1000 + remSum * 0.12 + nGain * 0.4;
  }

  /**
   * @param {string[]} poolV 現在の未開示 multiset（sessionKeys は場で表向きとしてグローバルと整合）
   */
  function cpuMaxValueThisTurnImperfect(sessionKeys, poolV, depth) {
    const t = handTotal(sessionKeys, pictureMode, aceMode);
    if (t > 21) return -1e18;
    if (t === 21) return 1e15 + sessionKeys.length;

    const standU = cpuUtilityIfStandNow(sessionKeys, poolV);
    if (depth <= 0) return standU;

    const indices = sampleSlotIndicesForCpu(faceDownSlotIndices());
    if (indices.length === 0) return standU;

    let best = standU;
    for (let x = 0; x < indices.length; x++) {
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

    const sampleKeys =
      pool.length <= CPU_MAX_POOL_SAMPLES
        ? pool.slice()
        : shuffle(pool.slice()).slice(0, CPU_MAX_POOL_SAMPLES);

    let sum = 0;
    for (let pi = 0; pi < sampleKeys.length; pi++) {
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
    }
    return sum / sampleKeys.length;
  }

  /**
   * 最適行動: 取得して終了 vs 次にめくるスロット
   * @returns {{ stand: true } | { flip: number }}
   */
  function cpuChooseStandOrFlip() {
    const sessionKeys = sessionIndices.map((i) => slots[i].key);
    const indicesAll = faceDownSlotIndices();
    const pool = buildRemainingUnknownPool();

    if (indicesAll.length === 0) {
      return { stand: true };
    }

    const indices = sampleSlotIndicesForCpu(indicesAll);

    if (sessionKeys.length === 0) {
      let bestIdx = -1;
      let bestVal = -Infinity;
      for (let x = 0; x < indices.length; x++) {
        const idx = indices[x];
        const v = cpuMarginalFlipValue(idx, [], pool, CPU_SEARCH_DEPTH);
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
    let bestFlip = null;
    let bestVal = -Infinity;
    for (let x = 0; x < indices.length; x++) {
      const idx = indices[x];
      const v = cpuMarginalFlipValue(idx, sessionKeys, pool, CPU_SEARCH_DEPTH);
      if (v > bestVal) {
        bestVal = v;
        bestFlip = idx;
      }
    }

    if (bestFlip === null) {
      return { stand: true };
    }
    if (standU >= bestVal) {
      return { stand: true };
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

  function runCpuStep() {
    if (!cpuEnabled || !isCpuTurn()) return;
    if (interactionLocked) {
      scheduleCpuTurn();
      return;
    }
    if (phase === "outcomeReveal") return;
    if (phase !== "idle" && phase !== "decide") return;

    setMessage(
      "CPUが取得済みの情報から期待値を計算し、最適手を選んでいます…"
    );

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
        if (decision.stand) {
          executeStandAndAdvance();
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

  function updateSessionUI() {
    const keys = sessionIndices.map((i) => slots[i].key);
    const total = keys.length ? handTotal(keys, pictureMode, aceMode) : 0;
    const hint = handRulesHint(pictureMode, aceMode);
    if (keys.length === 0) {
      elSession.innerHTML = "めくった札: なし " + hint;
    } else {
      elSession.innerHTML =
        'めくった札の合計: <strong>' +
        total +
        "</strong> " +
        hint +
        ' <span class="session-cards">' +
        escapeHtml(keys.join(" ")) +
        "</span>";
    }

    if (isCpuTurn()) {
      btnStand.disabled = true;
    } else if (phase === "decide") {
      btnStand.disabled = sessionIndices.length === 0;
    } else {
      btnStand.disabled = true;
    }
  }

  function createGrid() {
    elGrid.innerHTML = "";
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

  function hintDecideMessage() {
    if (faceDownOnFieldCount() > 0) {
      return isCpuTurn()
        ? "CPUのターンです。"
        : "伏せ札をクリックして追加、または「取得してターン終了」を選んでください。";
    }
    return "場に伏せ札がありません。「取得してターン終了」でターンを終了してください。";
  }

  /**
   * @returns {boolean} バストまたは21で収束したら true
   */
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
    setMessage(
      "バスト（合計 " + t + "）。「確認完了」をクリックしてください。"
    );
    updateSessionUI();
    refreshCpuPlayClass();
    if (isCpuTurn()) {
      window.setTimeout(function () {
        confirmOutcome();
      }, cpuRevealDelayMs);
    }
  }

  function beginOutcomeTwentyOne() {
    phase = "outcomeReveal";
    outcomeKind = "twentyone";
    btnStand.disabled = true;
    btnOutcomeOk.classList.remove("hidden");
    const n = sessionIndices.length;
    setMessage(
      "合計21（" +
        n +
        "枚）！めくった札を確認し、「確認完了」で取得して続行します。"
    );
    updateSessionUI();
    refreshCpuPlayClass();
    if (isCpuTurn()) {
      window.setTimeout(function () {
        confirmOutcome();
      }, cpuRevealDelayMs);
    }
  }

  function confirmOutcome() {
    if (phase !== "outcomeReveal") return;
    if (outcomeKind === "bust") {
      const toReset = sessionIndices.slice();
      sessionIndices = [];
      outcomeKind = null;
      phase = "idle";
      btnOutcomeOk.classList.add("hidden");
      toReset.forEach(function (idx) {
        slots[idx].flipped = false;
        syncSlotDOM(idx);
      });
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
        setMessage("CPUが取得しました。CPUのターン継続です。");
        scheduleCpuTurn();
      } else {
        setMessage(
          "取得完了。もう一度あなたのターンです。場から札をめくってください。"
        );
      }
    }
  }

  function executeStandAndAdvance() {
    if (phase !== "decide" || sessionIndices.length === 0) return;
    const took = sessionIndices.length;

    if (cpuEnabled && isCpuTurn() && cpuRevealDelayMs > 0) {
      interactionLocked = true;
      btnStand.disabled = true;
      const secDisp = (cpuRevealDelayMs / 1000).toFixed(1).replace(/\.0$/, "");
      setMessage(
        "CPUが " +
          took +
          " 枚を取得します。めくった札を確認できます（約 " +
          secDisp +
          " 秒）…"
      );
      window.setTimeout(function () {
        if (phase !== "decide" || sessionIndices.length === 0) return;
        executeStandAndAdvanceApply(took);
      }, cpuRevealDelayMs);
      return;
    }

    executeStandAndAdvanceApply(took);
  }

  function executeStandAndAdvanceApply(took) {
    interactionLocked = true;
    phase = "idle";
    btnStand.disabled = true;

    sessionIndices.forEach(function (idx) {
      players[currentPlayer].collectedKeys.push(slots[idx].key);
      slots[idx].removed = true;
      slots[idx].flipped = false;
      syncSlotDOM(idx);
    });
    sessionIndices = [];

    setMessage(
      players[currentPlayer].name + "が " + took + " 枚取得してターン終了。"
    );

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
    executeStandAndAdvance();
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
    sessionIndices = [];
    phase = "idle";
    outcomeKind = null;
    interactionLocked = false;

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
  }

  btnStand.addEventListener("click", standAndTake);
  btnOutcomeOk.addEventListener("click", confirmOutcome);

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
      playerCount = 0;
      document.querySelectorAll(".setup-row .btn-ghost").forEach((b) => {
        b.classList.remove("selected");
      });
      btnStart.disabled = true;
    }
  });

  document.querySelectorAll(".setup-row .btn-ghost").forEach((btn) => {
    btn.addEventListener("click", () => {
      if (cpuCheckbox && cpuCheckbox.checked) return;
      document.querySelectorAll(".setup-row .btn-ghost").forEach((b) => {
        b.classList.remove("selected");
      });
      btn.classList.add("selected");
      playerCount = parseInt(btn.getAttribute("data-players"), 10);
      btnStart.disabled = false;
    });
  });

  if (cpuCheckbox) {
    cpuCheckbox.addEventListener("change", function () {
      const row = playerCountRow;
      refreshCpuExtraSetupVisibility();
      if (cpuCheckbox.checked) {
        applyCpuSetupUiState();
      } else {
        if (row) {
          row.querySelectorAll("button").forEach(function (bt) {
            bt.disabled = false;
          });
        }
        playerCount = 0;
        btnStart.disabled = true;
        document.querySelectorAll(".setup-row .btn-ghost").forEach((b) => {
          b.classList.remove("selected");
        });
      }
    });
    refreshCpuExtraSetupVisibility();
  }

  btnStart.addEventListener("click", () => {
    readSetupOptions();
    if (cpuEnabled) {
      if (playerCount !== 2) playerCount = 2;
    } else if (playerCount < 2) {
      return;
    }
    startGame();
  });
})();
