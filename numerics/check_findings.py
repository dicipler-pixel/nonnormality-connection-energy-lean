"""Numerical sanity checks for FINDINGS_INVENTORY.md (branch findings-v2).

Each block prints PASS/FAIL-style lines; "PAPER CLAIM REFUTED" marks a checked error in an original.
Deterministic: seed 20261018. Run: python3 numerics/check_findings.py
"""
import numpy as np, itertools, math
rng = np.random.default_rng(20261018)
fro = np.linalg.norm
def comm(X, Y): return X @ Y - Y @ X
def herm(r): X = rng.normal(size=(r, r)) + 1j*rng.normal(size=(r, r)); return (X + X.conj().T)/2
def sym(r): X = rng.normal(size=(r, r)); return (X + X.T)/2
def skew(r): X = rng.normal(size=(r, r)); return (X - X.T)/2
def unit(r):
    Q, R = np.linalg.qr(rng.normal(size=(r, r)) + 1j*rng.normal(size=(r, r)))
    return Q*(np.diag(R)/abs(np.diag(R)))
J = np.array([[0., 1.], [-1., 0.]])
def hdr(s): print("\n== " + s)

# ---------- L1. lattice transport A = alpha J Delta_1 ----------
hdr("L1  A = alpha*(Delta_1 (x) J) is symmetric; spectrum -/+ 2 alpha sin(2 pi k/N)")
def Delta1(N):
    S = np.roll(np.eye(N), 1, axis=1)          # (S psi)_n = psi_{n+1}
    return S - S.T
for N in (6, 7, 12):
    al = 0.7; A = al*np.kron(Delta1(N), J)
    ev = np.sort(np.linalg.eigvals(A).real)
    pred = np.sort(np.concatenate([2*al*np.sin(2*np.pi*np.arange(N)/N), -2*al*np.sin(2*np.pi*np.arange(N)/N)]))
    print(f"N={N}: |A-A^T|={fro(A-A.T):.1e}  max|imag eig|={abs(np.linalg.eigvals(A).imag).max():.1e}  spectrum err={abs(ev-pred).max():.1e}")

# ---------- L2. exact commutator for H = S + eps E ----------
hdr("L2  [H,H^T] = eps[E-E^T,S] + eps^2[E,E^T] exactly; skew E => 2 eps [E,S] (no eps^2 term)")
n = 8; S = sym(n); E = rng.normal(size=(n, n)); K = skew(n)
for eps in (1e-1, 1e-3):
    H = S + eps*E; lhs = comm(H, H.T); rhs = eps*comm(E - E.T, S) + eps**2*comm(E, E.T)
    Hk = S + eps*K; lk = comm(Hk, Hk.T)
    print(f"eps={eps}: general err={fro(lhs-rhs):.1e}; skew: err vs 2eps[K,S]={fro(lk-2*eps*comm(K,S)):.1e}, ||[H,H^T]||/eps={fro(lk)/eps:.6f}")
print("normal iff [K,S]=0: K commuting with S ->", fro(comm(S+0.3*(S@S-S@S.T), (S+0.3*(S@S-S@S.T)).T)) < 1e-12)

# ---------- L3. 2x2 anticommutator: MJ+JM = tr(M) J ----------
hdr("L3  MJ+JM = tr(M) J for symmetric 2x2 M; MJ-JM symmetric; paper's matrix = JM-MJ")
a, b, d = rng.normal(size=3); M = np.array([[a, b], [b, d]])
print("MJ+JM - tr(M)J =", fro(M@J + J@M - np.trace(M)*J))
paper = np.array([[2*b, d-a], [d-a, -2*b]])
print("paper [[2b,d-a],[d-a,-2b]] - (JM-MJ) =", fro(paper - (J@M - M@J)), "; paper - (MJ+JM) =", round(fro(paper-(M@J+J@M)), 3), "-> PAPER CLAIM REFUTED (723a sec.10.4)")
print("trace-free M (a=-d) gives MJ+JM =", fro(np.array([[1., .5], [.5, -1.]])@J + J@np.array([[1., .5], [.5, -1.]])), "(E_lead sees only the trace of the gradient)")

# ---------- lattice model ----------
def lattice(N, al, Bs, eps, avg=True):
    A = al*np.kron(Delta1(N), J)
    D0 = np.zeros((2*N, 2*N)); El = np.zeros_like(D0); Ea = np.zeros_like(D0)
    for n_ in range(N):
        D0[2*n_:2*n_+2, 2*n_:2*n_+2] = Bs[n_]
        Mn = (Bs[(n_+1) % N] - Bs[n_-1])/2
        El[2*n_:2*n_+2, 2*n_:2*n_+2] = Mn@J + J@Mn
    dB = [Bs[(n_+1) % N] - Bs[n_] for n_ in range(N)]
    for n_ in range(N):   # (E_avg psi)_n = 1/4[dB_n J(psi_{n+1}+psi_n) + dB_{n-1} J(psi_n+psi_{n-1})]
        for (m, blk) in (((n_+1) % N, dB[n_]@J), (n_, dB[n_]@J + dB[n_-1]@J), ((n_-1) % N, dB[n_-1]@J)):
            Ea[2*n_:2*n_+2, 2*m:2*m+2] += blk/4
    E = El + (Ea if avg else 0)
    return A + D0, El, Ea, A + D0 + eps*E
hdr("L4  Paper's E = E_lead + E_avg: skew part only sees tr(dB); E_avg enters at O(eps)")
N = 10
Bs = [np.array([[2+0.6*np.cos(2*np.pi*k/N), 0.4*np.sin(2*np.pi*k/N)], [0.4*np.sin(2*np.pi*k/N), 2-0.6*np.cos(2*np.pi*k/N)]]) for k in range(N)]  # trace constant, anisotropic
H0, El, Ea, _ = lattice(N, 1.0, Bs, 0.0)
print("trace-constant anisotropic B_n: ||E_lead|| =", f"{fro(El):.1e}", " ||E_avg|| =", f"{fro(Ea):.3f}", " ||E_avg - E_avg^T|| =", f"{fro(Ea-Ea.T):.1e}")
H = H0 + 0.05*(El+Ea); print("  => H symmetric, ||[H,H^T]|| =", f"{fro(comm(H, H.T)):.1e}: anisotropy alone produces NO non-normality (contradicts the Delta_n story)")
Bs = [np.array([[2+0.6*np.cos(2*np.pi*k/N), 0.4], [0.4, 2.5+0.3*np.sin(2*np.pi*k/N)]]) for k in range(N)]  # trace varies
H0, El, Ea, _ = lattice(N, 1.0, Bs, 0.0)
for eps in (1e-2, 1e-3, 1e-4):
    Hl = H0 + eps*El; Hf = H0 + eps*(El+Ea)
    dlt = fro(comm(Hf, Hf.T) - comm(Hl, Hl.T))
    print(f"eps={eps:g}: ||[H,H^T]_full - [H,H^T]_lead-only|| = {dlt:.3e}, /eps = {dlt/eps:.4f} (constant => O(eps), not O(eps^2)) -> PAPER CLAIM REFUTED")
hdr("L5  Eigenvalues leave the real axis (claimed to stay real, 48b2/69c4 Fig. captions)")
Bc = [np.eye(2)*2.0 for _ in range(N)]
H0c = 1.0*np.kron(Delta1(N), J) + np.kron(np.eye(N), 2*np.eye(2))
Kp = skew(2*N)
for eps in (1e-1, 1e-2, 1e-3):
    ev = np.linalg.eigvals(H0c + eps*Kp)
    print(f"eps={eps:g}: max|Im lambda| = {abs(ev.imag).max():.3e} (ratio/eps {abs(ev.imag).max()/eps:.3f})")
H0g, El, Ea, Hg = lattice(N, 1.0, [np.diag([2+0.6*np.cos(2*np.pi*k/N)+0.3*np.sin(4*np.pi*k/N), 2.5]) for k in range(N)], 0.05)
print("paper's own E=E_lead+E_avg, eps=0.05: max|Im lambda| =", f"{abs(np.linalg.eigvals(Hg).imag).max():.3e}")

hdr("L6  Pseudospectral bulge height is O(eps) (Bauer-Fike), not O(sqrt eps)")
def smin(z, H): return np.linalg.svd(z*np.eye(len(H)) - H, compute_uv=False)[-1]
eta = 1e-3
for eps in (4e-2, 1e-2, 2.5e-3):
    H = H0c + eps*Kp; lam = np.linalg.eigvals(H); h = 0.0
    for l in lam:
        lo_, hi_ = 0.0, 1.0
        if smin(l.real + 1j*abs(l.imag), H) > eta: continue
        lo_ = abs(l.imag)
        for _ in range(50):
            mid = (lo_+hi_)/2
            if smin(l.real+1j*mid, H) <= eta: lo_ = mid
            else: hi_ = mid
        h = max(h, lo_)
    print(f"eps={eps:g}: eta-pseudospectrum height = {h:.5f}; Bauer-Fike bound eta+eps||E||_2 = {eta+eps*np.linalg.norm(Kp,2):.5f}; (h-eta)/eps = {(h-eta)/eps:.3f}, (h-eta)/sqrt(eps) = {(h-eta)/math.sqrt(eps):.3f}")
EE = El + Ea
hdr("L7  Kreiss constant: RHP version infinite, dist version bounded (eigvec cond.)")
for eps in (1e-1, 1e-2, 1e-3, 1e-4):
    H = H0g + eps*EE; w, V = np.linalg.eig(H)
    print(f"eps={eps:g}: max Re lambda = {w.real.max():.3f} (>0 => sup_Re z>0 Re z||R(z)|| = inf), cond(V) = {np.linalg.cond(V):.3f}  (dist-Kreiss <= cond(V); no 1/sqrt(eps) growth)")

hdr("L8  'Gauge invariance' B_n -> U_n B_n U_n^T with A fixed (723a sec.10.4, 81cd Prop.5)")
H1 = np.eye(2); print("alpha=0, B=I, U=2I: spec", np.linalg.eigvalsh(H1), "->", np.linalg.eigvalsh(2*H1@(2*H1).T), "-> PAPER CLAIM REFUTED (GL(2))")
Bs3 = [np.diag([1+0.5*k/N, 2.0]) for k in range(N)]
_, _, _, H = lattice(N, 1.0, Bs3, 0.0)
th = rng.uniform(0, 2*np.pi, N)
R = lambda t: np.array([[np.cos(t), -np.sin(t)], [np.sin(t), np.cos(t)]])
Bs3r = [R(t)@B@R(t).T for t, B in zip(th, Bs3)]
_, _, _, Hr = lattice(N, 1.0, Bs3r, 0.0)
print("site-dependent SO(2) rotations of B_n, A fixed: spectral change =", f"{abs(np.sort(np.linalg.eigvalsh(H))-np.sort(np.linalg.eigvalsh(Hr))).max():.3f}", "-> refuted for local U_n")
U = np.kron(np.eye(N), R(0.83)); Bs3c = [R(0.83)@B@R(0.83).T for B in Bs3]
_, _, _, Hc = lattice(N, 1.0, Bs3c, 0.0)
print("constant U in SO(2): ||U H U^T - H'|| =", f"{fro(U@H@U.T-Hc):.1e}", "(exact orthogonal similarity; TRUE restricted version)")
Rf = np.diag([1., -1.]); print("reflection: Rf J Rf^T = -J ->", fro(Rf@J@Rf.T + J) == 0)

hdr("C1  Connection-energy kernel dimensions on the 4-cycle, r=3 (v1)")
def kernel_dim(edges, n, r, A):
    basis = []
    for i in range(r):
        for j in range(r):
            X = np.zeros((r, r), complex)
            if i == j: X[i, i] = 1; basis.append(X)
            elif i < j:
                X[i, j] = X[j, i] = 1; basis.append(X.copy())
                Y = np.zeros((r, r), complex); Y[i, j] = 1j; Y[j, i] = -1j; basis.append(Y)
    cols = []
    for v in range(n):
        for B in basis:
            Ds = [np.zeros((r, r), complex) for _ in range(n)]; Ds[v] = B
            col = np.concatenate([(Ds[i] - A[(i, j)]@Ds[j]@A[(i, j)].conj().T).ravel() for (i, j) in edges])
            cols.append(np.concatenate([col.real, col.imag]))
    Mx = np.array(cols).T
    return Mx.shape[1] - np.linalg.matrix_rank(Mx, tol=1e-9)
edges = [(0, 1), (1, 2), (2, 3), (3, 0)]
Ag = {e: unit(3) for e in edges}; print("generic unitaries: dim =", kernel_dim(edges, 4, 3, Ag), "(v1 says 3)")
th0 = 0.9; Ah = {e: np.eye(3, dtype=complex) for e in edges}; Ah[(3, 0)] = np.diag([1, 1, np.exp(1j*th0)])
print("holonomy diag(1,1,e^{i theta}): dim =", kernel_dim(edges, 4, 3, Ah), "(v1 says 5)")
Ah2 = {e: Ag[e] for e in edges}; W = Ag[(0, 1)]@Ag[(1, 2)]@Ag[(2, 3)]
Ah2[(3, 0)] = (W.conj().T)  # flat: trivial holonomy
print("trivial holonomy: dim =", kernel_dim(edges, 4, 3, Ah2), "(= 9 = dim Herm(3))")

hdr("C2  Non-unitary edges: normal iff D_i A_ij = A_ij D_j (v1 kernel corollary)")
r = 2; D0_ = herm(r); P = rng.normal(size=(r, r)) + 1j*rng.normal(size=(r, r))
Hb = np.block([[D0_, P], [-P.conj().T, D0_]]); print("commuting D0 with generic invertible P (fails D_iA=AD_j): ||[H,H*]|| =", f"{fro(comm(Hb, Hb.conj().T)):.3f}")
Pc = 2*np.eye(r) + 0.5*D0_; Hc2 = np.block([[D0_, Pc], [-Pc.conj().T, D0_]]); print("P commuting with D0 (D_iA=AD_j holds): ||[H,H*]|| =", f"{fro(comm(Hc2, Hc2.conj().T)):.1e}")

hdr("C3  Scalar case and Fiedler bound (Dirichlet note, v1)")
n = 6; Ed = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0), (0, 3)]
d = rng.normal(size=n); w = {e: rng.normal()+1j*rng.normal() for e in Ed}
H = np.diag(d).astype(complex); L = np.zeros((n, n))
for (i, j), x in w.items():
    H[i, j] = x; H[j, i] = -np.conj(x); L[i, j] = L[j, i] = -abs(x)**2; L[i, i] += abs(x)**2; L[j, j] += abs(x)**2
lhs = fro(comm(H, H.conj().T))**2; lam2 = np.sort(np.linalg.eigvalsh(L))[1]; dc = d - d.mean()
print(f"||[H,H*]||^2 = {lhs:.5f}, 8 d^T L d = {8*d@L@d:.5f}, Fiedler lower bound 8 lam2 ||d-mean||^2 = {8*lam2*dc@dc:.5f}")
H2 = H.copy(); np.fill_diagonal(H2, np.full(n, 1.7)); print("constant d => normal:", fro(comm(H2, H2.conj().T)) < 1e-12)

hdr("C4  Rank-one aligned channels (Dirichlet note)")
r = 3; u = [np.linalg.qr(rng.normal(size=(r, 1)) + 1j*rng.normal(size=(r, 1)))[0][:, 0] for _ in range(2)]
dd = rng.normal(size=2); f = 0.8 - 0.3j
Ds = []
for k in range(2):
    Q, _ = np.linalg.qr(np.column_stack([u[k], rng.normal(size=(r, r-1))]))
    Ds.append(Q@np.diag([dd[k], *rng.normal(size=r-1)])@Q.conj().T)
Aij = f*np.outer(u[0], u[1].conj())
print("D_i A - A D_j - f(d_i-d_j) u_i u_j^* =", f"{fro(Ds[0]@Aij - Aij@Ds[1] - f*(dd[0]-dd[1])*np.outer(u[0], u[1].conj())):.1e}")

hdr("Q1  Quantum geometric tensor Q(V,W)=Tr(Pi V W), g=Re Q, Omega=-i Tr(Pi[V,W])")
nn, k = 5, 2; worst = 0; worstsat = 0
X = np.linalg.qr(rng.normal(size=(nn, k)) + 1j*rng.normal(size=(nn, k)))[0]; Pi = X@X.conj().T; Pc_ = np.eye(nn) - Pi
for _ in range(500):
    V = herm(nn); Wm = herm(nn)
    Q = np.trace(Pi@V@Wm); g = Q.real; Om = (-1j*np.trace(Pi@comm(V, Wm))).real
    assert abs(Q - (g + 0.5j*Om)) < 1e-12
    gVV = np.trace(Pi@V@V).real; gWW = np.trace(Pi@Wm@Wm).real
    worst = max(worst, abs(Om) - 2*math.sqrt(max(gVV*gWW - g**2, 0)))
print("Q = g + (i/2) Omega for all 500 random Hermitian pairs: True; Q = g + i Omega would fail (figure de7dd595 / 69c4 convention) -> PAPER CONVENTION ERROR")
print("max(|Omega| - 2 sqrt(gVV gWW - g^2)) over 500 pairs =", f"{worst:.2e} (<=0: inequality holds for ALL Hermitian V,W, not only tangent)")
Vt = Pi@herm(nn)@Pc_; Vt = Vt + Vt.conj().T
print("tangent V: g(V,V) - Tr(V^2)/2 =", f"{np.trace(Pi@Vt@Vt).real - np.trace(Vt@Vt).real/2:.1e}")
Wt = Pi@herm(nn)@Pc_; Wt = Wt + Wt.conj().T
Qc = np.trace(Pc_@Vt@Wt); Qp = np.trace(Pi@Vt@Wt)
print("complementary projector: Q_{1-Pi}(V,W) - conj Q_Pi(V,W) =", f"{abs(Qc-np.conj(Qp)):.1e} (g equal, Omega flips sign)")
for _ in range(200):     # two-band saturation
    x = np.linalg.qr(rng.normal(size=(2, 1)) + 1j*rng.normal(size=(2, 1)))[0]; P2 = x@x.conj().T; C2 = np.eye(2) - P2
    V2 = P2@herm(2)@C2; V2 += V2.conj().T; W2 = P2@herm(2)@C2; W2 += W2.conj().T
    Q2 = np.trace(P2@V2@W2); g2 = Q2.real; O2 = 2*Q2.imag
    gv = np.trace(P2@V2@V2).real; gw = np.trace(P2@W2@W2).real
    worstsat = max(worstsat, abs(abs(O2) - 2*math.sqrt(max(gv*gw-g2**2, 0))))
print("two-band (C^2, rank 1) tangent pairs: max | |Omega| - bound | =", f"{worstsat:.1e} (saturation, 81cd sec.12.6.1)")
P1 = Pi; X2 = np.linalg.qr(rng.normal(size=(nn, k)) + 1j*rng.normal(size=(nn, k)))[0]; P2 = X2@X2.conj().T
cos = np.linalg.svd(X.conj().T@X2, compute_uv=False)
print("Tr(Pi1 Pi2) - sum cos^2 theta_i =", f"{np.trace(P1@P2).real - (cos**2).sum():.1e} (81cd Thm 14)")

hdr("Q2  Localization index LPI = (N sum ||psi_n||^4)^-1 in [1/N, 1]")
Nn = 9; lo, hi = 1, 0
for _ in range(1000):
    psi = rng.normal(size=(Nn, 2)) * rng.exponential(size=(Nn, 1))**3; psi /= fro(psi)
    lpi = 1/(Nn*np.sum(np.sum(psi**2, 1)**2)); lo = min(lo, lpi); hi = max(hi, lpi)
print(f"over 1000 random states: min LPI = {lo:.4f} >= 1/N = {1/Nn:.4f}; max = {hi:.4f} <= 1")

hdr("T1  First-order cancellation & sign of second order (81cd Prop. 2, Lemma 5, Thm 8)")
n = 6; S = sym(n) + 4*np.eye(n); Kk = skew(n); lam = np.linalg.eigvalsh(S)
ld = lambda e: np.linalg.slogdet(S + e*Kk)[1]
print("det(S+eK) = det(S-eK):", abs(np.linalg.det(S+0.3*Kk) - np.linalg.det(S-0.3*Kk)) < 1e-9)
print(f"d/de log det at 0 (central diff) = {(ld(1e-4)-ld(-1e-4))/2e-4:.1e}")
w_, Vv = np.linalg.eigh(S); Kt = Vv.T@Kk@Vv
c2 = 0.5*sum(Kt[i, j]**2/(w_[i]*w_[j]) for i in range(n) for j in range(n) if i != j)
e = 1e-3; print(f"[log det(S+eK)-log det S]/e^2 = {(ld(e)-ld(0))/e**2:.6f}; predicted +1/2 sum|K_nm|^2/(l_n l_m) = {c2:.6f} > 0")
print("81cd Thm 8 predicts a NEGATIVE e^2 correction with gap^2 denominators -> PAPER CLAIM REFUTED (sign and denominators)")
z = 0.4+2.0j; Rt = lambda e: np.trace(np.linalg.inv(z*np.eye(n) - S - e*Kk))
G2 = -sum(Kt[i, j]**2/((z-w_[i])**2*(z-w_[j])) for i in range(n) for j in range(n) if i != j)
print(f"Lemma 5 check: [TrR(e)-TrR(0)]/e^2 = {(Rt(1e-3)-Rt(0))/1e-6:.5f}, G2 = {G2:.5f} (Lemma 5 is correct)")

hdr("T2  81cd Thm 3 (EP iff coalescence AND non-normal K) - counterexamples")
def is_diag(M, tol=1e-6):
    w, V = np.linalg.eig(M); return np.linalg.matrix_rank(V, tol=tol) == len(M)
K0 = np.zeros((2, 2)); At = np.block([[np.zeros((2, 2)), np.eye(2)], [-K0, np.zeros((2, 2))]])
print("K=0 (normal): A_true diagonalizable?", is_diag(At), "-> EP without non-normality")
K1 = np.array([[1., 0, 1], [0, 1, 0], [0, 0, 2]]); At1 = np.block([[np.zeros((3, 3)), np.eye(3)], [-K1, np.zeros((3, 3))]])
print("K=[[1,0,1],[0,1,0],[0,0,2]] (coalesced eigenvalue 1, ||[K,K^T]||=", f"{fro(comm(K1, K1.T)):.2f}) : A_true diagonalizable?", is_diag(At1), "-> no EP despite both conditions")

hdr("T3  81cd Lemma 10 at zero gradient")
m = 1.5; eps = 1e-2; print(f"dB=0: R = 1/(m+eps) = {1/(m+eps):.6f} < claimed lower bound 1/m = {1/m:.6f} (+O(eps^2)) -> PAPER CLAIM REFUTED")

hdr("F1  Filament Rev.4 Thm 4.1: ||exp(-Jt)|| for J=[[b,mu],[0,b]]")
def expm(M, terms=80):
    out = np.eye(len(M)); term = np.eye(len(M))
    for k_ in range(1, terms): term = term@M/k_; out = out + term
    return out
b, mu = 1.0, 3.0; err = 0
for t in np.linspace(0, 5, 51):
    sc = max(1, int(np.ceil(np.linalg.norm(np.array([[b, mu], [0, b]])*t)))); Et = np.linalg.matrix_power(expm(-np.array([[b, mu], [0, b]])*t/sc), sc)
    err = max(err, abs(np.linalg.norm(Et, 2) - math.exp(-b*t)*(math.sqrt(4+mu**2*t**2)+mu*t)/2))
print(f"max formula error = {err:.1e}")
Mf = lambda t: math.exp(-b*t)*(math.sqrt(4+mu**2*t**2)+mu*t)/2
kap = mu/b; ts = math.sqrt(kap**2-4)/mu; Mx = (kap+math.sqrt(kap**2-4))/2*math.exp(-math.sqrt(kap**2-4)/kap)
print(f"t* = {ts:.5f}, Mmax = {Mx:.5f}, grid max of formula = {max(Mf(t) for t in np.linspace(0, 3, 30001)):.5f}")
lo_, hi_ = 0.1, 0.99
for _ in range(80):
    mid = (lo_+hi_)/2
    if (1-mid-math.exp(-2*mid)) > 0: lo_ = mid
    else: hi_ = mid
x = lo_; print(f"kappa_r: x = {x:.11f}, kappa_r = {1/math.sqrt(x*(1-x)):.11f} (paper 0.79681213002, 2.48526751266)")
hdr("X1  Continuum limit: second difference error <= delta^2 ||psi''''|| / 12")
f4 = lambda t: np.sin(3*t); d2 = lambda t: -9*np.sin(3*t)
for dl in (0.1, 0.05, 0.025):
    t = np.linspace(0.5, 2.5, 101); e = abs((f4(t+dl)-2*f4(t)+f4(t-dl))/dl**2 - d2(t)).max()
    print(f"delta={dl}: max err {e:.3e}, bound {dl**2*81/12:.3e}")
