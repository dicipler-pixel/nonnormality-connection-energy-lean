# SCRIPT: TWO-BOOKS-MAP-01
# E- = sum_E ||D_i - U_ij(D_j)||^2 (connection energy), E+ = sum_E ||D_i + U_ij(D_j)||^2 (the opposite).
# Each claim below is followed by why the check proves it. Kill: any error above 1e-10, or any bound broken.
# T1 (light: one edge is one step). Scalar positive field: per edge E-/E+ = Gamma^2 with
#    Gamma = (d_i - d_j)/(d_i + d_j) = tanh(ln(d_i/d_j)/2), the step reflection and the peel coordinate.
#    E+ - E- = 4 d_i d_j, the transmitted part: (Y1-Y2)^2 + 4Y1Y2 = (Y1+Y2)^2 is the flux balance.
# T2 (passive fields): if every D_i is positive semidefinite, each edge has E-_e <= E+_e, so |Gamma_e| <= 1;
#    E-_e = 0 is a matched edge, E-_e = E+_e a mirror edge. Checked on random PSD fields and random unitaries.
# T3 (boundaries: the double cover). On the bipartite double cover (vertices (i,+),(i,-), each edge {i,j}
#    lifted to (i,+)-(j,-) and (i,-)-(j,+) with the same transport), a field F = (S+T, S-T) has cover
#    connection energy 2 E-(S) + 2 E+(T), with no cross term: the two books are the even and odd halves of one
#    connection energy on the double cover.
# T4 (bipartite swap): on a bipartite graph, flipping the sign of D on one side swaps E- and E+ exactly.
# T5 (the trade-off): E- + E+ = 2 sum_i deg(i) ||D_i||^2, so the transport H and the squared operator H^2
#    cannot be normal and Hermitian together unless D = 0.
import numpy as np
rng = np.random.default_rng(11)
F2 = lambda X: np.linalg.norm(X)**2
def herm(r): X = rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r)); return (X + X.conj().T)/2
def psd(r): X = rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r)); return X @ X.conj().T
def unit(r): Q, R = np.linalg.qr(rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r))); return Q*np.exp(1j*np.angle(np.diag(R)))
def graph(n, p=0.5):
    E = [(i, j) for i in range(n) for j in range(i+1, n) if rng.random() < p]
    return E or [(0, 1)]
def books(D, A, E):
    m = sum(F2(D[i] - A[e] @ D[j] @ A[e].conj().T) for e, (i, j) in enumerate(E))
    p = sum(F2(D[i] + A[e] @ D[j] @ A[e].conj().T) for e, (i, j) in enumerate(E))
    return m, p
# T1
w = 0.0
for _ in range(2000):
    di, dj = rng.uniform(0.01, 10, 2)
    G = (di - dj)/(di + dj)
    w = max(w, abs((di - dj)**2/(di + dj)**2 - G**2), abs(G - np.tanh(np.log(di/dj)/2)), abs((di + dj)**2 - (di - dj)**2 - 4*di*dj))
print(f'T1 one edge = one step (Gamma, tanh peel form, flux balance): max error {w:.1e}  {"PASS" if w < 1e-10 else "KILL"}')
# T2
viol = 0; mx = 0.0
for _ in range(3000):
    r = rng.integers(1, 5); Di, Dj, U = psd(r), psd(r), unit(r)
    m, p = F2(Di - U @ Dj @ U.conj().T), F2(Di + U @ Dj @ U.conj().T)
    mx = max(mx, m/p); viol += m > p + 1e-12
# mirror edge: orthogonal supports
Di = np.diag([1.0, 0]); Dj = np.diag([0, 1.0]); U = np.eye(2)
m, p = F2(Di - Dj), F2(Di + Dj)
print(f'T2 passive fields: {viol} violations of |Gamma_e| <= 1 in 3000 edges (largest ratio {mx:.4f}); orthogonal supports give ratio {m/p:.1f} (mirror)  {"PASS" if viol == 0 and abs(m/p - 1) < 1e-12 else "KILL"}')
# T3
w = 0.0
for _ in range(200):
    n, r = rng.integers(3, 7), rng.integers(1, 4); E = graph(n); A = [unit(r) for _ in E]
    S = [herm(r) for _ in range(n)]; T = [herm(r) for _ in range(n)]
    Fp = [S[i] + T[i] for i in range(n)]; Fm = [S[i] - T[i] for i in range(n)]
    cover = 0.0
    for e, (i, j) in enumerate(E):
        Ue = lambda X: A[e] @ X @ A[e].conj().T
        cover += F2(Fp[i] - Ue(Fm[j])) + F2(Fm[i] - Ue(Fp[j]))
    mS, _ = books(S, A, E); _, pT = books(T, A, E)
    w = max(w, abs(cover - 2*mS - 2*pT))
print(f'T3 double cover: cover energy = 2 E-(S) + 2 E+(T), max error {w:.1e}  {"PASS" if w < 1e-10 else "KILL"}')
# T4
w = 0.0
for _ in range(200):
    a, b, r = rng.integers(1, 4), rng.integers(1, 4), rng.integers(1, 4)
    E = [(i, a + j) for i in range(a) for j in range(b) if rng.random() < 0.7] or [(0, a)]
    A = [unit(r) for _ in E]; D = [herm(r) for _ in range(a + b)]
    m, p = books(D, A, E); D2 = [D[i] if i < a else -D[i] for i in range(a + b)]
    m2, p2 = books(D2, A, E); w = max(w, abs(m - p2), abs(p - m2))
print(f'T4 bipartite sign flip swaps the books: max error {w:.1e}  {"PASS" if w < 1e-10 else "KILL"}')
# T5
w = 0.0
for _ in range(200):
    n, r = rng.integers(3, 7), rng.integers(1, 4); E = graph(n); A = [unit(r) for _ in E]; D = [herm(r) for _ in range(n)]
    m, p = books(D, A, E); deg = np.zeros(n)
    for (i, j) in E: deg[i] += 1; deg[j] += 1
    w = max(w, abs(m + p - 2*sum(deg[i]*F2(D[i]) for i in range(n))))
print(f'T5 budget E- + E+ = 2 sum deg ||D_i||^2: max error {w:.1e}  {"PASS" if w < 1e-10 else "KILL"}')
