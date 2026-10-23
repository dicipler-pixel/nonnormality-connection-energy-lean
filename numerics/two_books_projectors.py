# SCRIPT: TWO-BOOKS-PROJECTORS-01
# When every vertex block is a rank-k orthogonal projector P_i, transport keeps it one (R = U P_j U* is a rank-k
# projector). Claim: per edge E- = 2 sum sin^2(theta_a) (the known principal-angle form, Penrose comparison
# bundle check 32/25), E+ = 2 sum (1 + cos^2 theta_a), so E+ = 4k - E- on every edge: for projector fields the
# opposite book carries no new information, and the visibility is V_e = (1/k) sum cos^2 theta_a.
# Why this proves it: principal angles come from the singular values of the cross-basis overlap, computed
# independently of the two Frobenius norms. Kill: any error above 1e-10.
import numpy as np
rng = np.random.default_rng(4)
def proj(n, k):
    Q, _ = np.linalg.qr(rng.normal(size=(n, k)) + 1j*rng.normal(size=(n, k))); return Q[:, :k], Q[:, :k] @ Q[:, :k].conj().T
w = 0
for _ in range(2000):
    n = rng.integers(2, 7); k = rng.integers(1, n+1)
    Qa, P = proj(n, k); Qb, R = proj(n, k)
    c2 = np.linalg.svd(Qa.conj().T @ Qb, compute_uv=False)**2
    Em, Ep = np.linalg.norm(P - R)**2, np.linalg.norm(P + R)**2
    w = max(w, abs(Em - 2*np.sum(1 - c2)), abs(Ep - 2*np.sum(1 + c2)), abs(Ep + Em - 4*k), abs((Ep - Em)/(Ep + Em) - np.sum(c2)/k))
print(f'projector fields: E- = 2 sum sin^2, E+ = 2 sum (1 + cos^2), E+ + E- = 4k, V = mean cos^2: max error {w:.1e}  {"PASS" if w < 1e-10 else "KILL"}')
