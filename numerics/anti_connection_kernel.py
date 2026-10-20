# SCRIPT: ANTI-CONNECTION-KERNEL-01
# Claim: the opposite energy sum_E ||D_i + U_ij(D_j)||^2 is the connection energy of the sign-twisted
# transport -U, so its zero set is the fields D_i0 with (-1)^len(C) W_C X W_C* = X for every loop C at i0.
# Test: cycles of length L with random unitary edges; kernel dimension of the quadratic form (computed
# from the matrices) must equal the dimension of {X in Herm(r): (-1)^L Ad_W X = X}. Kill: any mismatch.
import numpy as np
rng = np.random.default_rng(3)
def unit(r): Q, R = np.linalg.qr(rng.normal(size=(r,r)) + 1j*rng.normal(size=(r,r))); return Q*np.exp(1j*np.angle(np.diag(R)))
def herm_basis(r):
    B = []
    for a in range(r):
        M = np.zeros((r,r), complex); M[a,a] = 1; B.append(M)
        for b in range(a+1, r):
            M = np.zeros((r,r), complex); M[a,b] = M[b,a] = 1; B.append(M/np.sqrt(2))
            M = np.zeros((r,r), complex); M[a,b] = 1j; M[b,a] = -1j; B.append(M/np.sqrt(2))
    return B
def vec(X, B): return np.array([np.real(np.trace(b.conj().T @ X)) for b in B])
bad = 0
for L in [3, 4, 5, 6]:
    for r in [1, 2, 3]:
        for special in [False, True]:
            A = [unit(r) for _ in range(L)]
            if special and r == 2:   # make the holonomy sigma_z so an odd loop has an anti-fixed field
                A = [np.eye(2, dtype=complex) for _ in range(L-1)] + [np.diag([1, -1]).astype(complex)]
            B = herm_basis(r); m = len(B); N = L*m
            Q = np.zeros((N, N))
            for e in range(L):
                i, j = e, (e+1) % L
                Mi = np.zeros((m, N)); Mi[:, i*m:(i+1)*m] = np.eye(m)
                T = np.array([vec(A[e] @ b @ A[e].conj().T, B) for b in B]).T
                Mj = np.zeros((m, N)); Mj[:, j*m:(j+1)*m] = T
                R = Mi + Mj; Q += R.T @ R
            kdim = int(np.sum(np.linalg.eigvalsh(Q) < 1e-9))
            W = np.eye(r, dtype=complex)
            for e in reversed(range(L)): W = W @ A[e]
            # loop holonomy acting on the base field: transport around and compare
            Ad = np.array([vec(((-1)**L) * (W.conj().T @ b @ W), B) for b in B]).T
            pdim = int(np.sum(np.abs(np.linalg.eigvals(Ad - np.eye(m))) < 1e-9))
            ok = kdim == pdim; bad += not ok
            print(f'L={L} r={r} {"sigma_z holonomy" if special and r==2 else "random"}: kernel {kdim}, predicted {pdim}  {"ok" if ok else "MISMATCH"}')
print('PASS' if bad == 0 else f'KILL ({bad} mismatches)')
