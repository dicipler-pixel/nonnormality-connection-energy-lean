# SCRIPT: ANTI-CONNECTION-ENERGY-01
# Claim to test: with H = D + A on a graph (D_i Hermitian blocks, A_ij unitary, A_ji = -A_ij^dagger),
#   (1) 1/8 ||H H* - H* H||^2 = sum_E ||D_i - U_ij(D_j)||^2        (the known identity, control)
#   (2) 1/8 ||H^2 - (H*)^2||^2 = sum_E ||D_i + U_ij(D_j)||^2        (the opposite: anticommutator)
#   (3) (1) + (2) = 2 sum_E (||D_i||^2 + ||D_j||^2)                 (a fixed budget split two ways)
#   (4) scalar case: the opposite can vanish with D != 0 on an even cycle, never on an odd cycle
# Kill: any identity off by more than 1e-10 on 200 random graphs.
import numpy as np
rng = np.random.default_rng(7)
def herm(r): X = rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r)); return (X + X.conj().T)/2
def unit(r): Q, R = np.linalg.qr(rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r))); return Q*np.exp(1j*np.angle(np.diag(R)))
F = lambda X: np.linalg.norm(X)**2
worst = [0, 0, 0]
for trial in range(200):
    n, r = rng.integers(3, 8), rng.integers(1, 4)
    E = [(i, j) for i in range(n) for j in range(i+1, n) if rng.random() < 0.5] or [(0, 1)]
    D = [herm(r) for _ in range(n)]
    H = np.zeros((n*r, n*r), complex)
    for i in range(n): H[i*r:(i+1)*r, i*r:(i+1)*r] = D[i]
    Ab = {}
    for (i, j) in E:
        Aij = unit(r); Ab[(i, j)] = Aij
        H[i*r:(i+1)*r, j*r:(j+1)*r] = Aij; H[j*r:(j+1)*r, i*r:(i+1)*r] = -Aij.conj().T
    Hs = H.conj().T
    Uj = {e: Ab[e] @ D[e[1]] @ Ab[e].conj().T for e in E}
    minus = sum(F(D[i] - Uj[(i, j)]) for (i, j) in E)
    plus = sum(F(D[i] + Uj[(i, j)]) for (i, j) in E)
    budget = 2*sum(F(D[i]) + F(D[j]) for (i, j) in E)
    worst[0] = max(worst[0], abs(F(H@Hs - Hs@H)/8 - minus))
    worst[1] = max(worst[1], abs(F(H@H - Hs@Hs)/8 - plus))
    worst[2] = max(worst[2], abs(minus + plus - budget))
for k, w in zip(['(1) commutator = connection energy', '(2) H^2 - H*^2 = anti-connection energy', '(3) sum = fixed budget'], worst):
    print(f'{k}: max error {w:.1e}  {"PASS" if w < 1e-10 else "KILL"}')
# (4) scalar, trivial transport: anti-energy = sum (d_i + d_j)^2 = signless Laplacian form
for N in [4, 5, 6, 7]:
    Q = np.zeros((N, N))
    for i in range(N):
        j = (i+1) % N; Q[i, i] += 1; Q[j, j] += 1; Q[i, j] += 1; Q[j, i] += 1
    print(f'(4) cycle of {N}: smallest anti-energy eigenvalue {np.linalg.eigvalsh(Q)[0]:.3e}  ({"zero: alternating field fits" if N % 2 == 0 else "positive: odd loop frustrates"})')
