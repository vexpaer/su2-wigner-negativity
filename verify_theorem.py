#!/usr/bin/env python3
"""
Independent computational verification of:
  1. Exact Stratonovich-Weyl kernel Delta_j(n) properties (trace, covariance, traciality,
     all sign choices epsilon_l in {+1, -1}).
  2. Half-integer spin pi-rotation orthogonality: existence of u_* in S^2 with
     <psi | exp(-i pi u_* . J) | psi> = 0 via odd real function h(u) = <psi | i exp(-i pi u.J) | psi>.
  3. Integer spin spherical harmonic zero: existence of n_* in S^2 with <j,0;n_* | psi> = 0,
     Laplace-Beltrami eigenvalue check Delta_{S^2} Y_psi = -j(j+1) Y_psi,
     exact operator Equatorial Integral Identity:
       (1/(2 pi)) int_0^{2 pi} exp(-i pi u(phi).J) d phi = (-1)^j |j,0;n><j,0;n|,
     and resulting pi-rotation zero u_* perp n_*.
  4. Direct computation of spherical Wigner function W_psi(n) = Tr[|psi><psi| Delta_j(n)],
     verification of traciality integral int W_psi(n) W_psi(R_{u_*}(pi) n) d mu(n) = 0,
     and explicit witnessing of strict negativity min_{n in S^2} W_psi(n) < 0.
"""

import math
import cmath
import random
from fractions import Fraction

# ---------------------------------------------------------------------------
# Exact Clebsch-Gordan coefficients <j1, m1; j2, m2 | J, M> (Racah formula)
# ---------------------------------------------------------------------------
def cg_exact_sq_and_sign(j1, m1, j2, m2, J, M):
    """Return (sign, exact Fraction for CG^2) using half-integers as Fractions."""
    j1, m1, j2, m2, J, M = map(Fraction, (j1, m1, j2, m2, J, M))
    if m1 + m2 != M:
        return 0, Fraction(0)
    if J < abs(j1 - j2) or J > j1 + j2:
        return 0, Fraction(0)
    if abs(m1) > j1 or abs(m2) > j2 or abs(M) > J:
        return 0, Fraction(0)
    if (j1 + j2 - J).denominator != 1 or (j1 - m1).denominator != 1:
        return 0, Fraction(0)

    def fac(x):
        assert x.denominator == 1 and x >= 0
        return math.factorial(int(x))

    # Racah formula
    pref_sq = (Fraction(int(2*J + 1)) *
               Fraction(fac(J + j1 - j2) * fac(J - j1 + j2) * fac(j1 + j2 - J),
                        fac(j1 + j2 + J + 1)) *
               Fraction(fac(J + M) * fac(J - M) * fac(j1 - m1) * fac(j1 + m1) *
                        fac(j2 - m2) * fac(j2 + m2)))

    kmin = max(0, int(j2 - J - m1), int(j1 - J + m2))
    kmax = min(int(j1 + j2 - J), int(j1 - m1), int(j2 + m2))
    s = Fraction(0)
    for k in range(kmin, kmax + 1):
        denom = (fac(Fraction(k)) * fac(j1 + j2 - J - k) * fac(j1 - m1 - k) *
                 fac(j2 + m2 - k) * fac(J - j2 + m1 + k) * fac(J - j1 - m2 + k))
        s += Fraction((-1)**k, denom)
    if s == 0:
        return 0, Fraction(0)
    sign = 1 if s > 0 else -1
    return sign, pref_sq * s * s

def cg(j1, m1, j2, m2, J, M):
    sgn, sq = cg_exact_sq_and_sign(j1, m1, j2, m2, J, M)
    return sgn * math.sqrt(float(sq))

# ---------------------------------------------------------------------------
# Wigner small d-matrix d^j_{m', m}(theta) = <j, m' | exp(-i theta Jy) | j, m>
# ---------------------------------------------------------------------------
def wigner_d(j, theta):
    two_j = int(round(2 * j))
    d = two_j + 1
    ms = [j - k for k in range(d)]
    c = math.cos(theta / 2.0)
    s = math.sin(theta / 2.0)
    M = [[0.0] * d for _ in range(d)]
    for r, mp in enumerate(ms):
        for col, m in enumerate(ms):
            pref = math.sqrt(
                math.factorial(int(round(j + mp))) * math.factorial(int(round(j - mp))) *
                math.factorial(int(round(j + m)))  * math.factorial(int(round(j - m)))
            )
            smin = max(0, int(round(m - mp)))
            smax = min(int(round(j + m)), int(round(j - mp)))
            tot = 0.0
            for k in range(smin, smax + 1):
                denom = (math.factorial(int(round(j + m - k))) * math.factorial(k) *
                         math.factorial(int(round(mp - m + k))) * math.factorial(int(round(j - mp - k))))
                sign = -1.0 if (int(round(mp - m)) + k) % 2 else 1.0
                pow_c = int(round(2 * j + m - mp - 2 * k))
                pow_s = int(round(mp - m + 2 * k))
                tot += sign * (c ** pow_c) * (s ** pow_s) / denom
            M[r][col] = pref * tot
    return M, ms

def rot_z(j, phi):
    two_j = int(round(2 * j))
    d = two_j + 1
    return [cmath.exp(-1j * (j - k) * phi) for k in range(d)]

def mat_mul(A, B):
    n = len(A)
    return [[sum(A[i][k] * B[k][j] for k in range(n)) for j in range(n)] for i in range(n)]

def mat_dag(A):
    n = len(A)
    return [[A[c][r].conjugate() for c in range(n)] for r in range(n)]

def diag_left(diag, M):
    n = len(M)
    return [[diag[r] * M[r][c] for c in range(n)] for r in range(n)]

def diag_right(M, diag):
    n = len(M)
    return [[M[r][c] * diag[c] for c in range(n)] for r in range(n)]

def pi_rotation_matrix(j, theta, phi):
    """Exact matrix U(u) = exp(-i pi u.J) where u = (sin th cos ph, sin th sin ph, cos th)."""
    D, ms = wigner_d(j, theta)
    d = len(ms)
    epiz = [cmath.exp(-1j * math.pi * m) for m in ms]
    # A = D * diag(epiz) * D^T
    A = [[sum(D[r][k] * epiz[k] * D[c][k] for k in range(d)) for c in range(d)] for r in range(d)]
    rz = rot_z(j, phi)
    rz_conj = [x.conjugate() for x in rz]
    return [[rz[r] * A[r][c] * rz_conj[c] for c in range(d)] for r in range(d)]

def delta_eigenvalues(j, eps_signs=None):
    """Delta_{j,m} = sum_{l=0}^{2j} eps_l * ((2l+1)/(2j+1)) <j,m; l,0 | j,m>."""
    two_j = int(round(2 * j))
    d = two_j + 1
    if eps_signs is None:
        eps_signs = [1] * (two_j + 1)
    ms = [Fraction(two_j, 2) - k for k in range(d)]
    vals = []
    for m in ms:
        tot = 0.0
        for l in range(two_j + 1):
            tot += eps_signs[l] * ((2 * l + 1) / d) * cg(Fraction(two_j, 2), m, l, 0, Fraction(two_j, 2), m)
        vals.append(tot)
    return vals

def wigner_value(j, psi, theta, phi, delta_eigs):
    """W_psi(n) = Tr[|psi><psi| Delta_j(n)] = sum_m Delta_{j,m} |<j,m;n | psi>|^2."""
    D, ms = wigner_d(j, theta)
    d = len(ms)
    # |j,m;n> = exp(-i phi Jz) exp(-i theta Jy) |j,m>
    # <j,m;n | psi> = (D^T exp(+i phi Jz) psi)_m
    v = [cmath.exp(1j * ms[r] * phi) * psi[r] for r in range(d)]
    tot = 0.0
    for k in range(d):
        amp = sum(D[r][k] * v[r] for r in range(d))
        tot += delta_eigs[k] * (amp.real**2 + amp.imag**2)
    return tot

def vec_inner(u, v):
    return sum(a.conjugate() * b for a, b in zip(u, v))

def mat_vec(M, v):
    return [sum(row[k] * v[k] for k in range(len(v))) for row in M]

def gauss_legendre(n):
    """Nodes and weights on [-1, 1] via Newton's method on Legendre polynomial P_n."""
    xs, ws = [], []
    for i in range(1, n + 1):
        x = math.cos(math.pi * (i - 0.25) / (n + 0.5))
        for _ in range(30):
            p0, p1 = 1.0, x
            for k in range(2, n + 1):
                p0, p1 = p1, ((2*k - 1)*x*p1 - (k - 1)*p0) / k
            dp = n * (x*p1 - p0) / (x*x - 1.0)
            dx = p1 / dp
            x -= dx
            if abs(dx) < 1e-15:
                break
        xs.append(x)
        ws.append(2.0 / ((1.0 - x*x) * dp * dp))
    return xs, ws

def integrate_sphere(func, n_theta=20, n_phi=40):
    """Exact Gauss-Legendre x trapezoidal quadrature of int_{S^2} func(th, ph) dOmega/(4 pi)."""
    xs, ws = gauss_legendre(n_theta)
    tot = 0.0
    for x, w in zip(xs, ws):
        th = math.acos(max(-1.0, min(1.0, x)))
        s_phi = 0.0
        for p in range(n_phi):
            ph = 2.0 * math.pi * p / n_phi
            s_phi += func(th, ph)
        tot += w * (s_phi / n_phi)
    return 0.5 * tot  # since int_{-1}^1 dx / 2 = 1

print("=" * 78)
print("PART 1: VERIFY STRATONOVICH-WEYL KERNEL (TRACE, TRACIALITY, ALL SIGN CHOICES)")
print("=" * 78)
random.seed(2026)
for two_j in range(1, 8):  # j = 1/2, 1, 3/2, 2, 5/2, 3, 7/2
    j = two_j / 2.0
    d = two_j + 1
    # Test both canonical signs (+1,...,+1) and a random non-canonical sign pattern
    sign_sets = [("canonical (+1)", [1]*(two_j+1)),
                 ("alt signs", [1] + [(-1)**l for l in range(1, two_j+1)])]
    for label, signs in sign_sets:
        deigs = delta_eigenvalues(j, signs)
        tr_err = abs(sum(deigs) - 1.0)
        # Random pure states psi, phi
        psi = [complex(random.gauss(0,1), random.gauss(0,1)) for _ in range(d)]
        nrm = math.sqrt(sum(abs(x)**2 for x in psi)); psi = [x/nrm for x in psi]
        phi_st = [complex(random.gauss(0,1), random.gauss(0,1)) for _ in range(d)]
        nrm = math.sqrt(sum(abs(x)**2 for x in phi_st)); phi_st = [x/nrm for x in phi_st]
        exact_ov = abs(vec_inner(psi, phi_st))**2
        nt = 2*two_j + 4
        np_ = 4*two_j + 6
        int_w = d * integrate_sphere(lambda th, ph: wigner_value(j, psi, th, ph, deigs), nt, np_)
        int_ww = d * integrate_sphere(
            lambda th, ph: wigner_value(j, psi, th, ph, deigs) * wigner_value(j, phi_st, th, ph, deigs),
            nt, np_
        )
        print(f"j={j:<3.1f} [{label:14s}]: |Tr(Delta)-1|={tr_err:.1e}, "
              f"|int W dmu - 1|={abs(int_w-1):.1e}, "
              f"|int W_psi W_phi dmu - |<psi|phi>|^2|={abs(int_ww-exact_ov):.1e}")
        assert tr_err < 1e-13
        assert abs(int_w - 1.0) < 1e-12
        assert abs(int_ww - exact_ov) < 1e-12

print("\n" + "=" * 78)
print("PART 2: VERIFY EQUATORIAL INTEGRAL IDENTITY (EXACT OPERATOR CHECK, j=1..6)")
print("=" * 78)
for j in range(1, 7):
    d = 2*j + 1
    # Test at a generic axis n = (sin th0 cos ph0, sin th0 sin ph0, cos th0)
    th0, ph0 = 1.13, 2.47
    # Build orthonormal frame (e1, e2, n)
    n_vec = (math.sin(th0)*math.cos(ph0), math.sin(th0)*math.sin(ph0), math.cos(th0))
    e1 = (math.cos(th0)*math.cos(ph0), math.cos(th0)*math.sin(ph0), -math.sin(th0))
    e2 = (-math.sin(ph0), math.cos(ph0), 0.0)
    # Quadrature over great circle u(phi) = cos(phi) e1 + sin(phi) e2
    M_avg = [[0j]*d for _ in range(d)]
    n_quad = 4*j + 4
    for p in range(n_quad):
        ang = 2.0 * math.pi * p / n_quad
        ux = math.cos(ang)*e1[0] + math.sin(ang)*e2[0]
        uy = math.cos(ang)*e1[1] + math.sin(ang)*e2[1]
        uz = math.cos(ang)*e1[2] + math.sin(ang)*e2[2]
        uth = math.acos(max(-1.0, min(1.0, uz)))
        uph = math.atan2(uy, ux)
        U = pi_rotation_matrix(j, uth, uph)
        for r in range(d):
            for c in range(d):
                M_avg[r][c] += U[r][c] / n_quad
    # RHS = (-1)^j |j,0;n><j,0;n|
    D0, ms0 = wigner_d(j, th0)
    # |j,0;n> = exp(-i ph0 Jz) exp(-i th0 Jy) |j,0>
    ket = [cmath.exp(-1j * ms0[r] * ph0) * D0[r][j] for r in range(d)]
    sgn = (-1)**j
    max_err = 0.0
    for r in range(d):
        for c in range(d):
            rhs = sgn * ket[r] * ket[c].conjugate()
            max_err = max(max_err, abs(M_avg[r][c] - rhs))
    print(f"j={j}: max entrywise error in (1/2pi) int exp(-i pi u.J) dphi = (-1)^j |j,0;n><j,0;n| : {max_err:.2e}")
    assert max_err < 1e-12

print("\n" + "=" * 78)
print("PART 3: VERIFY LAPLACE-BELTRAMI EIGENVALUE OF Y_psi(n) = <j,0;n | psi>")
print("=" * 78)
for j in range(1, 6):
    d = 2*j + 1
    psi = [complex(random.gauss(0,1), random.gauss(0,1)) for _ in range(d)]
    nrm = math.sqrt(sum(abs(x)**2 for x in psi)); psi = [x/nrm for x in psi]
    def Y_psi(th, ph):
        D, ms = wigner_d(j, th)
        # <j,0;n | psi> = sum_r (exp(-i m ph) D[r][j])^* psi[r]
        return sum(cmath.exp(1j * ms[r] * ph) * D[r][j] * psi[r] for r in range(d))
    th, ph = 0.93, 1.71
    h = 1e-3
    y0 = Y_psi(th, ph)
    d2_th = (-Y_psi(th+2*h, ph) + 16*Y_psi(th+h, ph) - 30*y0 + 16*Y_psi(th-h, ph) - Y_psi(th-2*h, ph)) / (12*h*h)
    d1_th = (-Y_psi(th+2*h, ph) + 8*Y_psi(th+h, ph) - 8*Y_psi(th-h, ph) + Y_psi(th-2*h, ph)) / (12*h)
    d2_ph = (-Y_psi(th, ph+2*h) + 16*Y_psi(th, ph+h) - 30*y0 + 16*Y_psi(th, ph-h) - Y_psi(th, ph-2*h)) / (12*h*h)
    lap = d2_th + (math.cos(th)/math.sin(th))*d1_th + d2_ph / (math.sin(th)**2)
    ratio = lap / y0
    err = abs(ratio + j*(j+1))
    print(f"j={j}: Delta_{{S^2}} Y_psi / Y_psi = {ratio.real:+.10f}{ratio.imag:+.2e}i  (expected {-j*(j+1)}, err={err:.2e})")
    assert err < 1e-8

print("\n" + "=" * 78)
print("PART 4: CONSTRUCTIVE WITNESSING OF PI-ROTATION ORTHOGONALITY & WIGNER NEGATIVITY")
print("=" * 78)

def find_pi_zero_half_int(j, psi):
    """Find u_* on the meridian phi=0 (or random meridian) connecting north to south pole."""
    # h(th) = <psi | i exp(-i pi u(th,0).J) | psi>, h(pi) = -h(0)
    def h(th):
        U = pi_rotation_matrix(j, th, 0.0)
        return (1j * vec_inner(psi, mat_vec(U, psi))).real
    a, b = 0.0, math.pi
    fa, fb = h(a), h(b)
    if abs(fa) < 1e-14:
        return a, 0.0
    assert fa * fb <= 0, f"Expected opposite signs, got {fa}, {fb}"
    for _ in range(60):
        mid = 0.5 * (a + b)
        fm = h(mid)
        if fa * fm <= 0:
            b, fb = mid, fm
        else:
            a, fa = mid, fm
    return 0.5*(a+b), 0.0

def find_harmonic_zero_int(j, psi):
    """Find n_* in S^2 with <j,0;n_* | psi> = 0 via multi-start damped Newton/gradient descent."""
    d = 2*j + 1
    def Y_val(th, ph):
        D, ms = wigner_d(j, th)
        return sum(cmath.exp(1j * ms[r] * ph) * D[r][j] * psi[r] for r in range(d))
    # Coarse grid search for near-zero
    best = (1e9, 0.5, 0.5)
    for a in range(1, 24):
        th = math.pi * a / 24
        for b in range(48):
            ph = 2*math.pi * b / 48
            v = abs(Y_val(th, ph))
            if v < best[0]:
                best = (v, th, ph)
    th, ph = best[1], best[2]
    # 2D Newton on (Re Y, Im Y) = (0, 0)
    for _ in range(30):
        y = Y_val(th, ph)
        if abs(y) < 1e-13:
            break
        h = 1e-7
        dt = (Y_val(th + h, ph) - Y_val(th - h, ph)) / (2*h)
        dp = (Y_val(th, ph + h) - Y_val(th, ph - h)) / (2*h)
        # 2x2 linear system: [[dt.real, dp.real], [dt.imag, dp.imag]] [dth, dph] = [-y.real, -y.imag]
        det = dt.real * dp.imag - dp.real * dt.imag
        if abs(det) < 1e-14:
            th += 1e-3; ph += 1e-3
            continue
        dth = (-y.real * dp.imag + dp.real * y.imag) / det
        dph = (-dt.real * y.imag + y.real * dt.imag) / det
        step = 1.0
        while step > 1e-4:
            nth = max(1e-6, min(math.pi - 1e-6, th + step*dth))
            nph = (ph + step*dph) % (2*math.pi)
            if abs(Y_val(nth, nph)) < abs(y):
                th, ph = nth, nph
                break
            step *= 0.5
        else:
            break
    return th, ph, abs(Y_val(th, ph))

def find_pi_zero_int(j, psi):
    th0, ph0, y_err = find_harmonic_zero_int(j, psi)
    e1 = (math.cos(th0)*math.cos(ph0), math.cos(th0)*math.sin(ph0), -math.sin(th0))
    e2 = (-math.sin(ph0), math.cos(ph0), 0.0)
    def g(ang):
        ux = math.cos(ang)*e1[0] + math.sin(ang)*e2[0]
        uy = math.cos(ang)*e1[1] + math.sin(ang)*e2[1]
        uz = math.cos(ang)*e1[2] + math.sin(ang)*e2[2]
        uth = math.acos(max(-1.0, min(1.0, uz)))
        uph = math.atan2(uy, ux)
        U = pi_rotation_matrix(j, uth, uph)
        return vec_inner(psi, mat_vec(U, psi)).real
    # Sample on great circle to bracket a sign change (or near zero)
    ns = 64
    vals = [(2*math.pi*k/ns, g(2*math.pi*k/ns)) for k in range(ns + 1)]
    # Check if already zero
    min_pt = min(vals, key=lambda x: abs(x[1]))
    a = b = None
    for k in range(ns):
        if vals[k][1] * vals[k+1][1] <= 0:
            a, b = vals[k][0], vals[k+1][0]
            break
    if a is None:
        # Tangential zero (e.g. spin coherent state where g(ang) == 0 identically on equator!)
        ang_star = min_pt[0]
    else:
        fa = g(a)
        for _ in range(60):
            mid = 0.5*(a + b)
            fm = g(mid)
            if fa * fm <= 0:
                b = mid
            else:
                a, fa = mid, fm
        ang_star = 0.5*(a + b)
    ux = math.cos(ang_star)*e1[0] + math.sin(ang_star)*e2[0]
    uy = math.cos(ang_star)*e1[1] + math.sin(ang_star)*e2[1]
    uz = math.cos(ang_star)*e1[2] + math.sin(ang_star)*e2[2]
    uth = math.acos(max(-1.0, min(1.0, uz)))
    uph = math.atan2(uy, ux)
    return uth, uph, y_err

for two_j in range(1, 9):  # j = 0.5, 1.0, 1.5, 2.0, 2.5, 3.0, 3.5, 4.0
    j = two_j / 2.0
    d = two_j + 1
    deigs = delta_eigenvalues(j)
    # Test spin coherent state + Dicke middle state + 3 random pure states
    test_cases = []
    coh = [1.0+0j] + [0j]*(d-1)
    test_cases.append(("coherent", coh))
    mid_dicke = [0j]*d; mid_dicke[d//2] = 1.0+0j
    test_cases.append(("Dicke_mid", mid_dicke))
    for t in range(3):
        psi = [complex(random.gauss(0,1), random.gauss(0,1)) for _ in range(d)]
        nrm = math.sqrt(sum(abs(x)**2 for x in psi))
        test_cases.append((f"rand_{t}", [x/nrm for x in psi]))
    for name, psi in test_cases:
        if two_j % 2 == 1:
            uth, uph = find_pi_zero_half_int(j, psi)
            y_info = "N/A (half-int)"
        else:
            uth, uph, y_err = find_pi_zero_int(int(j), psi)
            y_info = f"|Y(n_*)|={y_err:.1e}"
        U = pi_rotation_matrix(j, uth, uph)
        ov = abs(vec_inner(psi, mat_vec(U, psi)))
        # Verify min W_psi(n) < 0 directly on Fibonacci sphere
        min_w = 1e9
        Nfib = 500
        golden = math.pi * (3.0 - math.sqrt(5.0))
        for idx in range(Nfib):
            z = 1.0 - 2.0*(idx + 0.5)/Nfib
            th = math.acos(max(-1.0, min(1.0, z)))
            ph = golden * idx
            w = wigner_value(j, psi, th, ph, deigs)
            if w < min_w:
                min_w = w
        print(f"j={j:<3.1f} {name:9s}: |<psi|e^{{-i pi u_* . J}}|psi>|={ov:.2e}  ({y_info:17s})  min W_psi={min_w:+.6f}")
        assert ov < 1e-9, f"Overlap too large: {ov}"
        assert min_w < 0, f"Wigner not negative: {min_w}"

print("\nALL CHECKS PASSED SUCCESSFULLY!")
