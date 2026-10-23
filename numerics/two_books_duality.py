# SCRIPT: TWO-BOOKS-DUALITY-01
# Per edge put a = D_i, b = U_ij(D_j) (Hermitian, so <a,b> = Tr(ab) is real). Define
#   P_e = (||a||^2 - ||b||^2)/(||a||^2 + ||b||^2)        (which side carries more: predictability)
#   V_e = (E+_e - E-_e)/(E+_e + E-_e) = 2<a,b>/(||a||^2 + ||b||^2)   (difference of the books: visibility)
#   L_e^2 = 4 (||a||^2 ||b||^2 - <a,b>^2)/(||a||^2 + ||b||^2)^2    (a Gram determinant: the third leg)
# Claim: P_e^2 + V_e^2 + L_e^2 = 1 exactly (the triality form used in Price of a Direction), so P^2 + V^2 <= 1
# with equality iff b = lambda a (lambda real: parallel or anti-parallel up to scale). For scalar fields (r = 1)
# the third leg is identically 0. Why this proves it: all three are computed from the matrices, and the sum is
# checked against 1 on random edges; the r = 1 and aligned cases are separate controls.
# Kill: |sum - 1| > 1e-12 anywhere, or L > 1e-12 for r = 1, or L > 1e-12 when b = lambda a.
import numpy as np
rng = np.random.default_rng(9)
def herm(r): X = rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r)); return (X + X.conj().T)/2
def unit(r): Q, R = np.linalg.qr(rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r))); return Q*np.exp(1j*np.angle(np.diag(R)))
ip = lambda x, y: np.trace(x.conj().T @ y)
def legs(a, b):
    na, nb = np.real(ip(a, a)), np.real(ip(b, b)); s = na + nb; g = ip(a, b)
    Em, Ep = np.linalg.norm(a - b)**2, np.linalg.norm(a + b)**2
    P = (na - nb)/s; V = (Ep - Em)/(Ep + Em); L2 = 4*(na*nb - abs(g)**2)/s**2
    return P, V, L2, abs(np.imag(g))
w = 0; wim = 0; w1 = 0; wal = 0
for _ in range(5000):
    r = rng.integers(1, 5); a = herm(r); U = unit(r); b = U @ herm(r) @ U.conj().T
    P, V, L2, im = legs(a, b); w = max(w, abs(P*P + V*V + L2 - 1)); wim = max(wim, im)
    if r == 1: w1 = max(w1, abs(L2))
    lam = rng.uniform(-3, 3); P, V, L2, _ = legs(a, lam*a); wal = max(wal, abs(L2))
print(f'P^2 + V^2 + L^2 = 1 on 5000 random edges: max error {w:.1e}; Im<a,b> max {wim:.1e}  {"PASS" if w < 1e-12 else "KILL"}')
print(f'r = 1 (scalar field): third leg max {w1:.1e}  {"PASS" if w1 < 1e-12 else "KILL"}')
print(f'b = lambda a (aligned or anti-aligned): third leg max {wal:.1e}  {"PASS" if wal < 1e-12 else "KILL"}')
