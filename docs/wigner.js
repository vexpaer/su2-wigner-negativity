/**
 * Exact SU(2) Stratonovich-Weyl Spherical Wigner Explorer
 * Computes exact Racah Clebsch-Gordan kernel eigenvalues Delta_{j,m},
 * exact Wigner-D rotations, W_psi(n) on S^2, integrated negativity delta(psi),
 * and an explicit orthogonalizing pi-rotation axis u_* with <psi|exp(-i*pi u_* . J)|psi> = 0.
 */

(function () {
  "use strict";

  // --- Complex arithmetic helpers ---
  const c = (re, im = 0) => [re, im];
  const cAdd = (a, b) => [a[0] + b[0], a[1] + b[1]];
  const cSub = (a, b) => [a[0] - b[0], a[1] - b[1]];
  const cMul = (a, b) => [a[0] * b[0] - a[1] * b[1], a[0] * b[1] + a[1] * b[0]];
  const cConj = (a) => [a[0], -a[1]];
  const cAbs2 = (a) => a[0] * a[0] + a[1] * a[1];
  const cExpI = (phi) => [Math.cos(phi), Math.sin(phi)];

  const FACT = [1];
  for (let i = 1; i <= 25; i++) FACT[i] = FACT[i - 1] * i;
  const fact = (n) => (n < 0 ? 0 : FACT[Math.round(n)]);

  // Exact Racah Clebsch-Gordan <j1 m1; j2 m2 | J M> for integer/half-integer spins
  function clebschGordan(j1, m1, j2, m2, J, M) {
    if (Math.abs(m1 + m2 - M) > 1e-9) return 0;
    if (J < Math.abs(j1 - j2) - 1e-9 || J > j1 + j2 + 1e-9) return 0;
    if (Math.abs(m1) > j1 + 1e-9 || Math.abs(m2) > j2 + 1e-9 || Math.abs(M) > J + 1e-9) return 0;

    const num =
      (2 * J + 1) *
      fact(J + j1 - j2) *
      fact(J - j1 + j2) *
      fact(j1 + j2 - J) *
      fact(j1 + m1) *
      fact(j1 - m1) *
      fact(j2 + m2) *
      fact(j2 - m2) *
      fact(J + M) *
      fact(J - M);
    const den = fact(j1 + j2 + J + 1);
    const pref = Math.sqrt(num / den);

    const kMin = Math.max(0, Math.round(j2 - J - m1), Math.round(j1 + m2 - J));
    const kMax = Math.min(Math.round(j1 + j2 - J), Math.round(j1 - m1), Math.round(j2 + m2));

    let sum = 0;
    for (let k = kMin; k <= kMax; k++) {
      const termDen =
        fact(k) *
        fact(j1 + j2 - J - k) *
        fact(j1 - m1 - k) *
        fact(j2 + m2 - k) *
        fact(J - j2 + m1 + k) *
        fact(J - j1 - m2 + k);
      sum += (k % 2 === 0 ? 1 : -1) / termDen;
    }
    return pref * sum;
  }

  // Canonical Stratonovich-Weyl kernel eigenvalues Delta_{j,m} (epsilon_l = +1)
  function kernelEigenvalues(twoJ) {
    const j = twoJ / 2;
    const dim = twoJ + 1;
    const vals = new Float64Array(dim);
    for (let idx = 0; idx < dim; idx++) {
      const m = j - idx;
      let s = 0;
      for (let l = 0; l <= twoJ; l++) {
        s += ((2 * l + 1) / dim) * clebschGordan(j, m, l, 0, j, m);
      }
      vals[idx] = s;
    }
    return vals;
  }

  // Exact Wigner small-d matrix element d^j_{m', m}(beta)
  function wignerSmallD(twoJ, mp, m, beta) {
    const j = twoJ / 2;
    const cb = Math.cos(beta / 2);
    const sb = Math.sin(beta / 2);
    const pref = Math.sqrt(fact(j + mp) * fact(j - mp) * fact(j + m) * fact(j - m));
    const sMin = Math.max(0, Math.round(m - mp));
    const sMax = Math.min(Math.round(j + m), Math.round(j - mp));
    let total = 0;
    for (let s = sMin; s <= sMax; s++) {
      const sign = (mp - m + s) % 2 === 0 ? 1 : -1;
      const denom =
        fact(j + m - s) * fact(s) * fact(mp - m + s) * fact(j - mp - s);
      const powC = Math.round(2 * j + m - mp - 2 * s);
      const powS = Math.round(mp - m + 2 * s);
      total += (sign / denom) * Math.pow(cb, powC) * Math.pow(sb, powS);
    }
    return pref * total;
  }

  // Evaluate spherical Wigner function W_psi(theta, phi) using exact spectral form:
  // W_psi(n) = sum_m Delta_{j,m} |<j, m; n | psi>|^2
  // where |j, m; n> = exp(-i phi J_z) exp(-i theta J_y) |j, m>, so
  // <j, m; n | psi> = sum_{m'} d^j_{m', m}(theta) * e^{i m' phi} * psi_{m'}
  function evaluateWigner(twoJ, psi, deltaVals, theta, phi) {
    const j = twoJ / 2;
    const dim = twoJ + 1;
    // Pre-phase psi_{m'} * e^{i m' phi}
    const phasedRe = new Float64Array(dim);
    const phasedIm = new Float64Array(dim);
    for (let ip = 0; ip < dim; ip++) {
      const mp = j - ip;
      const cp = Math.cos(mp * phi);
      const sp = Math.sin(mp * phi);
      const re = psi[ip][0];
      const im = psi[ip][1];
      phasedRe[ip] = re * cp - im * sp;
      phasedIm[ip] = re * sp + im * cp;
    }

    let w = 0;
    for (let im = 0; im < dim; im++) {
      const m = j - im;
      let aRe = 0;
      let aIm = 0;
      for (let ip = 0; ip < dim; ip++) {
        const mp = j - ip;
        const dVal = wignerSmallD(twoJ, mp, m, theta);
        aRe += dVal * phasedRe[ip];
        aIm += dVal * phasedIm[ip];
      }
      w += deltaVals[im] * (aRe * aRe + aIm * aIm);
    }
    return w;
  }

  // Compute exact expectation value <psi | exp(-i pi u . J) | psi>
  // Note: exp(-i pi u . J) = R(phi, theta) exp(-i pi J_z) R(phi, theta)^dagger
  // Therefore <psi | exp(-i pi u . J) | psi> = sum_m e^{-i pi m} |<j, m; u | psi>|^2
  function piRotationOverlap(twoJ, psi, theta, phi) {
    const j = twoJ / 2;
    const dim = twoJ + 1;
    const phasedRe = new Float64Array(dim);
    const phasedIm = new Float64Array(dim);
    for (let ip = 0; ip < dim; ip++) {
      const mp = j - ip;
      const cp = Math.cos(mp * phi);
      const sp = Math.sin(mp * phi);
      phasedRe[ip] = psi[ip][0] * cp - psi[ip][1] * sp;
      phasedIm[ip] = psi[ip][0] * sp + psi[ip][1] * cp;
    }
    let outRe = 0;
    let outIm = 0;
    for (let im = 0; im < dim; im++) {
      const m = j - im;
      let aRe = 0;
      let aIm = 0;
      for (let ip = 0; ip < dim; ip++) {
        const mp = j - ip;
        const dVal = wignerSmallD(twoJ, mp, m, theta);
        aRe += dVal * phasedRe[ip];
        aIm += dVal * phasedIm[ip];
      }
      const prob = aRe * aRe + aIm * aIm;
      const phase = -Math.PI * m;
      outRe += Math.cos(phase) * prob;
      outIm += Math.sin(phase) * prob;
    }
    return [outRe, outIm];
  }

  // Real-valued pi-rotation expectation:
  // For half-integer j: h(u) = <psi | i exp(-i pi u.J) | psi> = -Im(<psi|exp(-i pi u.J)|psi>)
  // For integer j: g(u) = <psi | exp(-i pi u.J) | psi> = Re(<psi|exp(-i pi u.J)|psi>)
  function realPiValue(twoJ, psi, u) {
    const theta = Math.acos(Math.max(-1, Math.min(1, u[2])));
    const phi = Math.atan2(u[1], u[0]);
    const ov = piRotationOverlap(twoJ, psi, theta, phi);
    return twoJ % 2 === 1 ? -ov[1] : ov[0];
  }

  // Evaluate Y_psi(n) = <j, 0; n | psi> for integer j
  function evalYpsi(twoJ, psi, theta, phi) {
    const j = twoJ / 2;
    const dim = twoJ + 1;
    let aRe = 0;
    let aIm = 0;
    for (let ip = 0; ip < dim; ip++) {
      const mp = j - ip;
      const dVal = wignerSmallD(twoJ, mp, 0, theta);
      const cp = Math.cos(mp * phi);
      const sp = Math.sin(mp * phi);
      const pRe = psi[ip][0] * cp - psi[ip][1] * sp;
      const pIm = psi[ip][0] * sp + psi[ip][1] * cp;
      aRe += dVal * pRe;
      aIm += dVal * pIm;
    }
    return [aRe, aIm];
  }

  function normalizeVec3(v) {
    const len = Math.hypot(v[0], v[1], v[2]) || 1;
    return [v[0] / len, v[1] / len, v[2] / len];
  }

  function cross(a, b) {
    return [
      a[1] * b[2] - a[2] * b[1],
      a[2] * b[0] - a[0] * b[2],
      a[0] * b[1] - a[1] * b[0],
    ];
  }

  function orthoFrame(n) {
    const ref = Math.abs(n[2]) < 0.85 ? [0, 0, 1] : [1, 0, 0];
    const e1 = normalizeVec3(cross(ref, n));
    const e2 = normalizeVec3(cross(n, e1));
    return [e1, e2];
  }

  // Constructive search matching our exact proof!
  // Half-integer: bisect odd function h(u) from u0 to -u0.
  // Integer: locate zero n_* of Y_psi(n), then bisect real zero-mean g(phi) along equator u(phi) _|_ n_*.
  function findOrthogonalizingAxis(twoJ, psi) {
    if (twoJ % 2 === 1) {
      // Half-integer: start at z-axis, interpolate along meridian to -z
      const u0 = [0, 0, 1];
      const f0 = realPiValue(twoJ, psi, u0);
      if (Math.abs(f0) < 1e-10) return { uStar: u0, nStar: null, overlap: Math.abs(f0) };
      let lo = 0;
      let hi = Math.PI;
      let fLo = f0;
      for (let it = 0; it < 52; it++) {
        const mid = 0.5 * (lo + hi);
        const uMid = [Math.sin(mid), 0, Math.cos(mid)];
        const fMid = realPiValue(twoJ, psi, uMid);
        if (fLo * fMid <= 0) {
          hi = mid;
        } else {
          lo = mid;
          fLo = fMid;
        }
      }
      const t = 0.5 * (lo + hi);
      const uStar = [Math.sin(t), 0, Math.cos(t)];
      return { uStar, nStar: null, overlap: Math.abs(realPiValue(twoJ, psi, uStar)) };
    } else {
      // Integer spin: minimize |Y_psi(n)|^2 on S^2 via coarse grid + Nelder-Mead/coordinate refinement
      let bestTheta = 0.7;
      let bestPhi = 0.4;
      let bestVal = Infinity;
      const nT = 36;
      const nP = 72;
      for (let it = 0; it <= nT; it++) {
        const th = (Math.PI * it) / nT;
        for (let ip = 0; ip < nP; ip++) {
          const ph = (2 * Math.PI * ip) / nP;
          const y = evalYpsi(twoJ, psi, th, ph);
          const v = cAbs2(y);
          if (v < bestVal) {
            bestVal = v;
            bestTheta = th;
            bestPhi = ph;
          }
        }
      }
      // Coordinate-step refinement around best (theta, phi)
      let step = 0.08;
      for (let iter = 0; iter < 45; iter++) {
        let improved = false;
        const dirs = [
          [step, 0],
          [-step, 0],
          [0, step],
          [0, -step],
          [step, step],
          [-step, step],
          [step, -step],
          [-step, -step],
        ];
        for (const [dt, dp] of dirs) {
          const th = Math.max(0, Math.min(Math.PI, bestTheta + dt));
          const ph = bestPhi + dp;
          const v = cAbs2(evalYpsi(twoJ, psi, th, ph));
          if (v < bestVal) {
            bestVal = v;
            bestTheta = th;
            bestPhi = ph;
            improved = true;
          }
        }
        if (!improved) step *= 0.55;
        if (bestVal < 1e-18) break;
      }
      const nStar = [
        Math.sin(bestTheta) * Math.cos(bestPhi),
        Math.sin(bestTheta) * Math.sin(bestPhi),
        Math.cos(bestTheta),
      ];
      const [e1, e2] = orthoFrame(nStar);
      const uAt = (phi) => [
        Math.cos(phi) * e1[0] + Math.sin(phi) * e2[0],
        Math.cos(phi) * e1[1] + Math.sin(phi) * e2[1],
        Math.cos(phi) * e1[2] + Math.sin(phi) * e2[2],
      ];

      // Sample equator to find sign change of g(phi)
      const M = 180;
      let a = 0;
      let b = (2 * Math.PI) / M;
      let fa = realPiValue(twoJ, psi, uAt(0));
      let minAbsPhi = 0;
      let minAbsVal = Math.abs(fa);
      let bracketed = false;
      for (let k = 1; k <= M; k++) {
        const ph = (2 * Math.PI * k) / M;
        const fv = realPiValue(twoJ, psi, uAt(ph));
        if (Math.abs(fv) < minAbsVal) {
          minAbsVal = Math.abs(fv);
          minAbsPhi = ph;
        }
        if (fa * fv <= 0) {
          a = (2 * Math.PI * (k - 1)) / M;
          b = ph;
          bracketed = true;
          break;
        }
        fa = fv;
      }
      let phiStar = minAbsPhi;
      if (bracketed) {
        let fLo = realPiValue(twoJ, psi, uAt(a));
        for (let it = 0; it < 52; it++) {
          const mid = 0.5 * (a + b);
          const fMid = realPiValue(twoJ, psi, uAt(mid));
          if (fLo * fMid <= 0) {
            b = mid;
          } else {
            a = mid;
            fLo = fMid;
          }
        }
        phiStar = 0.5 * (a + b);
      }
      const uStar = uAt(phiStar);
      return {
        uStar,
        nStar,
        e1,
        e2,
        overlap: Math.abs(realPiValue(twoJ, psi, uStar)),
      };
    }
  }

  // Compute min W_psi and integrated negativity delta(psi) via fine spherical quadrature
  function computeWignerStats(twoJ, psi, deltaVals) {
    const nTh = 56;
    const nPh = 112;
    let minW = Infinity;
    let maxW = -Infinity;
    let intAbs = 0;
    const dTh = Math.PI / nTh;
    const dPh = (2 * Math.PI) / nPh;
    const normFactor = (twoJ + 1) / (4 * Math.PI);

    for (let it = 0; it < nTh; it++) {
      const th = (it + 0.5) * dTh;
      const sinTh = Math.sin(th);
      for (let ip = 0; ip < nPh; ip++) {
        const ph = ip * dPh;
        const w = evaluateWigner(twoJ, psi, deltaVals, th, ph);
        if (w < minW) minW = w;
        if (w > maxW) maxW = w;
        intAbs += Math.abs(w) * sinTh * dTh * dPh;
      }
    }
    const deltaNeg = Math.max(0, 0.5 * (normFactor * intAbs - 1));
    return { minW, maxW, deltaNeg };
  }

  // Normalize state vector
  function normalizeState(vec) {
    let s = 0;
    for (const z of vec) s += cAbs2(z);
    const inv = 1 / Math.sqrt(s || 1);
    return vec.map((z) => [z[0] * inv, z[1] * inv]);
  }

  // Preset pure states for any twoJ = 2j
  function buildPresetState(twoJ, preset) {
    const dim = twoJ + 1;
    const vec = Array.from({ length: dim }, () => [0, 0]);
    if (preset === "coherent") {
      // Spin coherent state |j, j>
      vec[0] = [1, 0];
      return { psi: vec, label: `|j=${twoJ / 2}, m=+${twoJ / 2}⟩ (spin coherent)` };
    }
    if (preset === "cat") {
      vec[0] = [Math.SQRT1_2, 0];
      vec[dim - 1] = [Math.SQRT1_2, 0];
      return {
        psi: vec,
        label: `(|+${twoJ / 2}⟩ + |−${twoJ / 2}⟩) / √2 (spin cat)`,
      };
    }
    if (preset === "dicke") {
      const mid = Math.floor(dim / 2);
      vec[mid] = [1, 0];
      const mVal = twoJ / 2 - mid;
      return {
        psi: vec,
        label: `|j=${twoJ / 2}, m=${mVal}⟩ (equatorial Dicke)`,
      };
    }
    if (preset === "special") {
      if (twoJ === 1) {
        vec[0] = [Math.SQRT1_2, 0];
        vec[1] = [0, Math.SQRT1_2];
        return { psi: vec, label: "(|+½⟩ + i|−½⟩) / √2 (|y+⟩)" };
      }
      if (twoJ === 2) {
        // Superposition of |1,1>, |1,0>, |1,-1> with nontrivial complex phase
        vec[0] = [0.6, 0];
        vec[1] = [0, 0.5];
        vec[2] = [0.6245, 0];
        return {
          psi: normalizeState(vec),
          label: "0.60|+1⟩ + 0.50i|0⟩ + 0.62|−1⟩ (asymmetric)",
        };
      }
      if (twoJ === 3) {
        // GHZ-like / 3-qubit W-like spin-3/2 state
        vec[1] = [Math.SQRT1_2, 0];
        vec[3] = [0, Math.SQRT1_2];
        return { psi: vec, label: "(|+½⟩ + i|−3/2⟩) / √2 (anticoherent)" };
      }
      // twoJ === 4: Tetrahedral (maximally anticoherent) spin-2 state
      vec[0] = [1 / Math.sqrt(3), 0];
      vec[3] = [Math.sqrt(2 / 3), 0];
      return {
        psi: vec,
        label: "(1/√3)|+2⟩ + √(2/3)|−1⟩ (tetrahedral anticoherent)",
      };
    }
    // Random Haar pure state
    for (let i = 0; i < dim; i++) {
      // Box-Muller complex Gaussian
      const u1 = Math.max(1e-12, Math.random());
      const u2 = Math.random();
      const r1 = Math.sqrt(-2 * Math.log(u1));
      const u3 = Math.max(1e-12, Math.random());
      const u4 = Math.random();
      const r2 = Math.sqrt(-2 * Math.log(u3));
      vec[i] = [r1 * Math.cos(2 * Math.PI * u2), r2 * Math.cos(2 * Math.PI * u4)];
    }
    const psi = normalizeState(vec);
    const comps = psi
      .map((z, idx) => {
        const m = twoJ / 2 - idx;
        const mag = Math.hypot(z[0], z[1]);
        return `${mag.toFixed(2)}e^{${Math.atan2(z[1], z[0]).toFixed(1)}i}|${m}⟩`;
      })
      .join(" + ");
    return { psi, label: `Haar random: ${comps}` };
  }

  // Diverging scientific colormap: vermilion negative <-> warm white 0 <-> deep cerulean positive
  function wignerColor(val, scale, highlightNeg) {
    const t = Math.max(-1, Math.min(1, val / scale));
    let r, g, b;
    if (t < 0) {
      const a = Math.pow(-t, 0.78);
      if (highlightNeg) {
        r = Math.round(247 + a * (168 - 247));
        g = Math.round(238 + a * (18 - 238));
        b = Math.round(232 + a * (18 - 232));
      } else {
        r = Math.round(247 + a * (178 - 247));
        g = Math.round(244 + a * (35 - 244));
        b = Math.round(238 + a * (24 - 238));
      }
    } else {
      const a = Math.pow(t, 0.82);
      r = Math.round(247 + a * (12 - 247));
      g = Math.round(244 + a * (72 - 244));
      b = Math.round(238 + a * (96 - 238));
    }
    return [r, g, b];
  }

  // Export for Node verification if loaded outside browser
  if (typeof window === "undefined") {
    module.exports = {
      kernelEigenvalues,
      evaluateWigner,
      findOrthogonalizingAxis,
      computeWignerStats,
      buildPresetState,
    };
    return;
  }

  // --- Browser Interactive Controller ---
  const canvas = document.getElementById("wigner-canvas");
  if (!canvas) return;
  const ctx = canvas.getContext("2d");

  const state = {
    twoJ: 2, // default j = 1 (shows both negative lobes AND equatorial great circle!)
    preset: "coherent",
    psi: null,
    stateLabel: "",
    deltaVals: null,
    stats: null,
    ortho: null,
    rotYaw: 0.58,
    rotPitch: 0.42,
    showAxis: true,
    showEquator: true,
    showNodal: true,
    dragging: false,
    lastX: 0,
    lastY: 0,
  };

  // Precomputed spherical grid for ultra-smooth 60fps drag rotation
  const GRID_T = 64;
  const GRID_P = 128;
  let wignerGrid = new Float64Array((GRID_T + 1) * GRID_P);

  function recomputePhysics() {
    state.deltaVals = kernelEigenvalues(state.twoJ);
    state.stats = computeWignerStats(state.twoJ, state.psi, state.deltaVals);
    state.ortho = findOrthogonalizingAxis(state.twoJ, state.psi);

    for (let it = 0; it <= GRID_T; it++) {
      const th = (Math.PI * it) / GRID_T;
      for (let ip = 0; ip < GRID_P; ip++) {
        const ph = (2 * Math.PI * ip) / GRID_P;
        wignerGrid[it * GRID_P + ip] = evaluateWigner(
          state.twoJ,
          state.psi,
          state.deltaVals,
          th,
          ph
        );
      }
    }
    updateReadout();
    renderSphere();
  }

  function sampleGrid(theta, phi) {
    let p = phi % (2 * Math.PI);
    if (p < 0) p += 2 * Math.PI;
    const ft = (theta / Math.PI) * GRID_T;
    const fp = (p / (2 * Math.PI)) * GRID_P;
    const it0 = Math.min(GRID_T - 1, Math.max(0, Math.floor(ft)));
    const ip0 = Math.floor(fp) % GRID_P;
    const ip1 = (ip0 + 1) % GRID_P;
    const dt = ft - it0;
    const dp = fp - Math.floor(fp);
    const w00 = wignerGrid[it0 * GRID_P + ip0];
    const w01 = wignerGrid[it0 * GRID_P + ip1];
    const w10 = wignerGrid[(it0 + 1) * GRID_P + ip0];
    const w11 = wignerGrid[(it0 + 1) * GRID_P + ip1];
    return (
      w00 * (1 - dt) * (1 - dp) +
      w01 * (1 - dt) * dp +
      w10 * dt * (1 - dp) +
      w11 * dt * dp
    );
  }

  // Camera transform: world (x,y,z) -> view (vx, vy, vz), with vz > 0 facing viewer
  function worldToView(v) {
    const cy = Math.cos(state.rotYaw);
    const sy = Math.sin(state.rotYaw);
    const cp = Math.cos(state.rotPitch);
    const sp = Math.sin(state.rotPitch);
    // Rotate around z by -yaw
    const x1 = cy * v[0] + sy * v[1];
    const y1 = -sy * v[0] + cy * v[1];
    const z1 = v[2];
    // Map standard physics coords (x forward, y right, z up) with pitch tilt
    const vx = y1;
    const vy = cp * z1 - sp * x1;
    const vz = sp * z1 + cp * x1;
    return [vx, vy, vz];
  }

  function viewToWorld(vx, vy, vz) {
    const cy = Math.cos(state.rotYaw);
    const sy = Math.sin(state.rotYaw);
    const cp = Math.cos(state.rotPitch);
    const sp = Math.sin(state.rotPitch);
    const x1 = -sp * vy + cp * vz;
    const y1 = vx;
    const z1 = cp * vy + sp * vz;
    const wx = cy * x1 - sy * y1;
    const wy = sy * x1 + cy * y1;
    const wz = z1;
    return [wx, wy, wz];
  }

  function renderSphere() {
    const size = 440;
    if (canvas.width !== size || canvas.height !== size) {
      canvas.width = size;
      canvas.height = size;
    }
    const cx = size / 2;
    const cy = size / 2;
    const R = size * 0.41;

    ctx.clearRect(0, 0, size, size);

    // Subtle grounding shadow beneath sphere
    const shadowGrad = ctx.createRadialGradient(cx, cy + R * 0.92, 10, cx, cy + R * 0.92, R * 0.78);
    shadowGrad.addColorStop(0, "rgba(23, 26, 33, 0.13)");
    shadowGrad.addColorStop(1, "rgba(23, 26, 33, 0)");
    ctx.fillStyle = shadowGrad;
    ctx.beginPath();
    ctx.ellipse(cx, cy + R * 0.96, R * 0.78, R * 0.16, 0, 0, 2 * Math.PI);
    ctx.fill();

    // Render shaded spherical Wigner map pixel-by-pixel
    const img = ctx.createImageData(size, size);
    const data = img.data;
    const scale = Math.max(Math.abs(state.stats.maxW), Math.abs(state.stats.minW), 0.15);
    const light = normalizeVec3([-0.32, 0.48, 0.82]);

    const xMin = Math.floor(cx - R - 1);
    const xMax = Math.ceil(cx + R + 1);
    const yMin = Math.floor(cy - R - 1);
    const yMax = Math.ceil(cy + R + 1);

    for (let py = yMin; py <= yMax; py++) {
      const vy = (cy - py) / R;
      const vy2 = vy * vy;
      for (let px = xMin; px <= xMax; px++) {
        const vx = (px - cx) / R;
        const r2 = vx * vx + vy2;
        if (r2 > 1.0) continue;
        const vz = Math.sqrt(Math.max(0, 1.0 - r2));
        const wv = viewToWorld(vx, vy, vz);
        const theta = Math.acos(Math.max(-1, Math.min(1, wv[2])));
        const phi = Math.atan2(wv[1], wv[0]);
        const val = sampleGrid(theta, phi);

        let [cr, cg, cb] = wignerColor(val, scale, state.showNodal);

        // Crisp nodal contour W_psi = 0
        if (state.showNodal && Math.abs(val) < scale * 0.022) {
          cr = Math.round(cr * 0.45);
          cg = Math.round(cg * 0.45);
          cb = Math.round(cb * 0.45);
        }

        // Subtle Lambertian + rim shading for 3D depth without obscuring colormap
        const ndotl = Math.max(0, vx * light[0] + vy * light[1] + vz * light[2]);
        const shade = 0.76 + 0.27 * ndotl;
        const idx = (py * size + px) * 4;
        data[idx] = Math.min(255, Math.round(cr * shade));
        data[idx + 1] = Math.min(255, Math.round(cg * shade));
        data[idx + 2] = Math.min(255, Math.round(cb * shade));
        // Anti-aliased edge alpha
        const edgeDist = (1 - Math.sqrt(r2)) * R;
        data[idx + 3] = edgeDist < 1.2 ? Math.round(255 * Math.max(0, edgeDist / 1.2)) : 255;
      }
    }
    ctx.putImageData(img, 0, 0);

    // Subtle sphere rim stroke
    ctx.strokeStyle = "rgba(23, 26, 33, 0.22)";
    ctx.lineWidth = 1.2;
    ctx.beginPath();
    ctx.arc(cx, cy, R, 0, 2 * Math.PI);
    ctx.stroke();

    // Subtle latitude/longitude graticule
    function drawCurve(points3D, color, lineWidth, dash = []) {
      ctx.save();
      ctx.strokeStyle = color;
      ctx.lineWidth = lineWidth;
      ctx.setLineDash(dash);
      let drawing = false;
      ctx.beginPath();
      for (const p of points3D) {
        const [vx, vy, vz] = worldToView(p);
        if (vz >= -0.02) {
          const sx = cx + vx * R;
          const sy = cy - vy * R;
          if (!drawing) {
            ctx.moveTo(sx, sy);
            drawing = true;
          } else {
            ctx.lineTo(sx, sy);
          }
        } else {
          drawing = false;
        }
      }
      ctx.stroke();
      ctx.restore();
    }

    // Equator z=0 & prime meridian
    const eqPts = [];
    const merPts = [];
    for (let i = 0; i <= 120; i++) {
      const a = (2 * Math.PI * i) / 120;
      eqPts.push([Math.cos(a), Math.sin(a), 0]);
      merPts.push([Math.cos(a), 0, Math.sin(a)]);
    }
    drawCurve(eqPts, "rgba(23, 26, 33, 0.14)", 1, [3, 4]);
    drawCurve(merPts, "rgba(23, 26, 33, 0.12)", 1, [3, 4]);

    // Integer spin: draw equatorial great circle u(phi) _|_ n_* and polar zero n_*
    if (state.showEquator && state.ortho && state.ortho.nStar) {
      const { e1, e2, nStar } = state.ortho;
      const greatCircle = [];
      for (let i = 0; i <= 140; i++) {
        const a = (2 * Math.PI * i) / 140;
        greatCircle.push([
          Math.cos(a) * e1[0] + Math.sin(a) * e2[0],
          Math.cos(a) * e1[1] + Math.sin(a) * e2[1],
          Math.cos(a) * e1[2] + Math.sin(a) * e2[2],
        ]);
      }
      drawCurve(greatCircle, "rgba(166, 106, 0, 0.9)", 2.2, [5, 3]);
      drawMarker(nStar, "n*", "#171a21", "#ffffff");
    }

    // Draw orthogonalizing pi-rotation axis u_* (and -u_*)
    if (state.showAxis && state.ortho && state.ortho.uStar) {
      const u = state.ortho.uStar;
      const negU = [-u[0], -u[1], -u[2]];
      drawAxisPin(u, "u*");
      drawAxisPin(negU, "-u*", true);
    }

    function drawMarker(vec, label, fill, stroke) {
      const [vx, vy, vz] = worldToView(vec);
      if (vz < -0.05) return;
      const sx = cx + vx * R;
      const sy = cy - vy * R;
      ctx.save();
      ctx.fillStyle = fill;
      ctx.strokeStyle = stroke;
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc(sx, sy, 5, 0, 2 * Math.PI);
      ctx.fill();
      ctx.stroke();
      ctx.font = '600 12px "JetBrains Mono", monospace';
      ctx.fillStyle = "#171a21";
      ctx.fillText(label, sx + 9, sy + 4);
      ctx.restore();
    }

    function drawAxisPin(vec, label, secondary = false) {
      const [vx, vy, vz] = worldToView(vec);
      if (vz < -0.05) return;
      const sx = cx + vx * R;
      const sy = cy - vy * R;
      const tipX = cx + vx * (R * 1.13);
      const tipY = cy - vy * (R * 1.13);
      ctx.save();
      ctx.strokeStyle = secondary ? "rgba(166, 106, 0, 0.55)" : "#a66a00";
      ctx.lineWidth = secondary ? 1.8 : 2.6;
      ctx.beginPath();
      ctx.moveTo(sx, sy);
      ctx.lineTo(tipX, tipY);
      ctx.stroke();

      ctx.fillStyle = secondary ? "#d8a138" : "#c77d00";
      ctx.strokeStyle = "#ffffff";
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.arc(sx, sy, secondary ? 4.5 : 6, 0, 2 * Math.PI);
      ctx.fill();
      ctx.stroke();

      ctx.font = '600 12px "JetBrains Mono", monospace';
      ctx.fillStyle = "#6e4400";
      ctx.fillText(label, tipX + (vx >= 0 ? 5 : -24), tipY + 4);
      ctx.restore();
    }
  }

  function updateReadout() {
    const minEl = document.getElementById("metric-min-w");
    const deltaEl = document.getElementById("metric-delta");
    const axisEl = document.getElementById("metric-axis");
    const ovEl = document.getElementById("metric-overlap");
    const formulaEl = document.getElementById("state-formula");
    const cbMin = document.getElementById("cb-min");
    const cbMax = document.getElementById("cb-max");
    const eqToggleWrap = document.getElementById("equator-toggle-wrap");

    if (minEl) minEl.textContent = state.stats.minW.toFixed(4);
    if (deltaEl) deltaEl.textContent = state.stats.deltaNeg.toFixed(4);
    if (axisEl && state.ortho) {
      const u = state.ortho.uStar;
      axisEl.textContent = `(${u[0].toFixed(3)}, ${u[1].toFixed(3)}, ${u[2].toFixed(3)})`;
    }
    if (ovEl && state.ortho) {
      ovEl.textContent = state.ortho.overlap.toExponential(2);
    }
    if (formulaEl) formulaEl.textContent = state.stateLabel;
    if (cbMin) cbMin.textContent = state.stats.minW.toFixed(2);
    if (cbMax) cbMax.textContent = `+${state.stats.maxW.toFixed(2)}`;
    if (eqToggleWrap) {
      eqToggleWrap.style.opacity = state.twoJ % 2 === 0 ? "1" : "0.45";
    }
  }

  function selectSpinAndPreset(twoJ, preset) {
    state.twoJ = twoJ;
    state.preset = preset;
    const built = buildPresetState(twoJ, preset);
    state.psi = built.psi;
    state.stateLabel = built.label;

    document.querySelectorAll(".seg-btn[data-twoj]").forEach((btn) => {
      btn.classList.toggle("active", Number(btn.dataset.twoj) === twoJ);
    });
    document.querySelectorAll(".preset-btn[data-preset]").forEach((btn) => {
      btn.classList.toggle("active", btn.dataset.preset === preset);
    });
    recomputePhysics();
  }

  // Bind UI controls
  document.querySelectorAll(".seg-btn[data-twoj]").forEach((btn) => {
    btn.addEventListener("click", () => {
      selectSpinAndPreset(Number(btn.dataset.twoj), state.preset);
    });
  });

  document.querySelectorAll(".preset-btn[data-preset]").forEach((btn) => {
    btn.addEventListener("click", () => {
      selectSpinAndPreset(state.twoJ, btn.dataset.preset);
    });
  });

  const randBtn = document.getElementById("btn-random-state");
  if (randBtn) {
    randBtn.addEventListener("click", () => {
      selectSpinAndPreset(state.twoJ, "random");
    });
  }

  const toggleAxis = document.getElementById("toggle-axis");
  if (toggleAxis) {
    toggleAxis.addEventListener("change", (e) => {
      state.showAxis = e.target.checked;
      renderSphere();
    });
  }
  const toggleEquator = document.getElementById("toggle-equator");
  if (toggleEquator) {
    toggleEquator.addEventListener("change", (e) => {
      state.showEquator = e.target.checked;
      renderSphere();
    });
  }
  const toggleNodal = document.getElementById("toggle-nodal");
  if (toggleNodal) {
    toggleNodal.addEventListener("change", (e) => {
      state.showNodal = e.target.checked;
      renderSphere();
    });
  }

  // Pointer drag rotation on canvas
  canvas.addEventListener("pointerdown", (e) => {
    state.dragging = true;
    state.lastX = e.clientX;
    state.lastY = e.clientY;
    canvas.setPointerCapture(e.pointerId);
  });
  canvas.addEventListener("pointermove", (e) => {
    if (!state.dragging) return;
    const dx = e.clientX - state.lastX;
    const dy = e.clientY - state.lastY;
    state.lastX = e.clientX;
    state.lastY = e.clientY;
    state.rotYaw += dx * 0.011;
    state.rotPitch = Math.max(-1.48, Math.min(1.48, state.rotPitch + dy * 0.011));
    renderSphere();
  });
  const endDrag = () => {
    state.dragging = false;
  };
  canvas.addEventListener("pointerup", endDrag);
  canvas.addEventListener("pointercancel", endDrag);

  // Copy BibTeX button
  const copyBtn = document.getElementById("copy-bibtex-btn");
  const bibEl = document.getElementById("bibtex-content");
  if (copyBtn && bibEl) {
    copyBtn.addEventListener("click", async () => {
      try {
        await navigator.clipboard.writeText(bibEl.textContent.trim());
        const prev = copyBtn.textContent;
        copyBtn.textContent = "Copied!";
        setTimeout(() => {
          copyBtn.textContent = prev;
        }, 1800);
      } catch {
        copyBtn.textContent = "Select & Copy";
      }
    });
  }

  // Initial state: spin j=1 coherent state (visually dramatic negative hemisphere + equatorial zero circle)
  selectSpinAndPreset(2, "coherent");
})();
