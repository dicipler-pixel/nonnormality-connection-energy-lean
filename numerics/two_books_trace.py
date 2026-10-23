# SCRIPT: TWO-BOOKS-TRACE-01
# His idea: our version of the constant term = light hiding and moving energy.
# Claim T1: split each block D_i = c_i I + T_i (T_i trace-free). Both books split exactly into a trace sector and a
#   trace-free sector with no cross term: E- = r sum (c_i - c_j)^2 + sum ||T_i - U T_j||^2,
#   E+ = r sum (c_i + c_j)^2 + sum ||T_i + U T_j||^2. (Cross terms vanish because Tr T = 0 and U preserves trace.)
# Claim T2: a uniform constant c (D_i = c I + T_i, same c everywhere) is invisible to the connection-energy book
#   (E- does not change) and lands entirely in the opposite book, which gains 4 r c^2 per edge plus a term linear in c
#   that is zero by T1. Equivalently, shifting H to H + cI leaves [H, H*] unchanged and moves H^2 - H*^2 by 4cA.
# Why this proves it: every quantity is computed from the full matrices; the predicted splits are compared numerically.
# Kill: any error above 1e-10.
import numpy as np
rng = np.random.default_rng(12)
F2 = lambda X: np.linalg.norm(X)**2
def herm(r): X = rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r)); return (X + X.conj().T)/2
def unit(r): Q, R = np.linalg.qr(rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r))); return Q*np.exp(1j*np.angle(np.diag(R)))
w1 = w2 = w3 = 0
for _ in range(300):
    n, r = rng.integers(3, 7), rng.integers(1, 4)
    E = [(i, j) for i in range(n) for j in range(i+1, n) if rng.random() < 0.5] or [(0, 1)]
    A = {e: unit(r) for e in E}; Dm = [herm(r) for _ in range(n)]
    c = [np.real(np.trace(X))/r for X in Dm]; T = [Dm[i] - c[i]*np.eye(r) for i in range(n)]
    Uf = lambda e, X: A[e] @ X @ A[e].conj().T
    Em = sum(F2(Dm[i] - Uf((i, j), Dm[j])) for i, j in E); Ep = sum(F2(Dm[i] + Uf((i, j), Dm[j])) for i, j in E)
    Em2 = sum(r*(c[i]-c[j])**2 + F2(T[i] - Uf((i, j), T[j])) for i, j in E)
    Ep2 = sum(r*(c[i]+c[j])**2 + F2(T[i] + Uf((i, j), T[j])) for i, j in E)
    w1 = max(w1, abs(Em - Em2), abs(Ep - Ep2))
    # T2 at the operator level
    H = np.zeros((n*r, n*r), complex); Aop = np.zeros_like(H)
    for i in range(n): H[i*r:(i+1)*r, i*r:(i+1)*r] = Dm[i]
    for (i, j) in E:
        Aop[i*r:(i+1)*r, j*r:(j+1)*r] = A[(i, j)]; Aop[j*r:(j+1)*r, i*r:(i+1)*r] = -A[(i, j)].conj().T
    H = H + Aop; cc = rng.normal(); Hc = H + cc*np.eye(n*r)
    comm = lambda X: X @ X.conj().T - X.conj().T @ X; sq = lambda X: X @ X - X.conj().T @ X.conj().T
    w2 = max(w2, np.linalg.norm(comm(Hc) - comm(H)))
    w3 = max(w3, np.linalg.norm(sq(Hc) - sq(H) - 4*cc*Aop))
print(f'T1 trace / trace-free split of both books: max error {w1:.1e}  {"PASS" if w1 < 1e-10 else "KILL"}')
print(f'T2 adding cI leaves [H,H*] unchanged: max change {w2:.1e}  {"PASS" if w2 < 1e-10 else "KILL"}')
print(f'T2 adding cI moves H^2 - H*^2 by exactly 4cA: max error {w3:.1e}  {"PASS" if w3 < 1e-10 else "KILL"}')
