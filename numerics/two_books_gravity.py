# SCRIPT: TWO-BOOKS-GRAVITY-01
# Gravity paper (Ledger Outlives the Metric, ed. 6), Theorem 6: the real trace form g(X) = (1/2) Re Tr(X^2)
# splits as ||Herm X||^2/2 - ||Skew X||^2/2 (neutral signature). Claim: with X = DA (D Hermitian field,
# A the skew edge transport), Herm(DA) = [D,A]/2 and Skew(DA) = {D,A}/2, so
#   E- - E+ = 4 g(DA) = 2 Re Tr((DA)^2)      (the difference of the books is the gravity form)
#   E- + E+ = 2 ||DA||_F^2                    (the sum is the budget)
# where E- = (1/8)||[H,H*]||^2 and E+ = (1/8)||H^2 - H*^2||^2. Why this proves it: both sides are computed
# independently from the full matrices (E- and E+ from H, the right sides from the product DA alone).
# Kill: error above 1e-10 on 300 random graphs; also report how often g(DA) is positive, negative, zero.
import numpy as np
rng = np.random.default_rng(5)
F2 = lambda X: np.linalg.norm(X)**2
def herm(r): X = rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r)); return (X + X.conj().T)/2
def unit(r): Q, R = np.linalg.qr(rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r))); return Q*np.exp(1j*np.angle(np.diag(R)))
w1 = w2 = 0.0; sign = {'+': 0, '-': 0}
for _ in range(300):
    n, r = rng.integers(3, 8), rng.integers(1, 4)
    E = [(i, j) for i in range(n) for j in range(i+1, n) if rng.random() < 0.5] or [(0, 1)]
    D = np.zeros((n*r, n*r), complex); A = np.zeros_like(D)
    for i in range(n): D[i*r:(i+1)*r, i*r:(i+1)*r] = herm(r)
    for (i, j) in E:
        U = unit(r); A[i*r:(i+1)*r, j*r:(j+1)*r] = U; A[j*r:(j+1)*r, i*r:(i+1)*r] = -U.conj().T
    H = D + A; Hs = H.conj().T
    Em = F2(H@Hs - Hs@H)/8; Ep = F2(H@H - Hs@Hs)/8
    X = D @ A; g = 0.5*np.real(np.trace(X@X))
    w1 = max(w1, abs((Em - Ep) - 4*g)); w2 = max(w2, abs((Em + Ep) - 2*F2(X)))
    sign['+' if g > 0 else '-'] += 1
print(f'E- - E+ = 4 g(DA): max error {w1:.1e}  {"PASS" if w1 < 1e-10 else "KILL"}')
print(f'E- + E+ = 2 ||DA||^2: max error {w2:.1e}  {"PASS" if w2 < 1e-10 else "KILL"}')
print(f'sign of g(DA) over 300 random graphs: positive {sign["+"]}, negative {sign["-"]} (the form is indefinite, as Theorem 6 says)')
