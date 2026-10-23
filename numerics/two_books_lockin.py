# SCRIPT: TWO-BOOKS-LOCKIN-01
# Ring of N nodes, field D_i = cos(t_i) sz + sin(t_i) sx, edge transport = rotation turning D by phi = d/N
# (the mixer's "universe" ring). Per edge: E- = 4(1 - cos(t_i - t_{i+1} - phi)), E+ = 4(1 + cos(...)).
# Claim A: the lowest reachable E- is min_w 4N(1 - cos((d - 2 pi w)/N)) (sync floor) and the lowest E+ is the
#          same with d replaced by d + N pi (anti-sync floor).
# Claim B: so for odd N the two floors interleave: whatever twist d frustrates one book, the other is freer;
#          the worst case of min(floor-, floor+) over all d is 4N(1 - cos(pi/(2N))), half the spacing of either alone.
# Why this proves it: floors are found by direct numerical minimisation from many random starts (gradient
# descent on the angles), independently of the formulas, then compared. Kill: any mismatch > 1e-6.
import numpy as np
rng = np.random.default_rng(2)
def minimise(N, d, sign, starts=40, steps=4000, lr=0.05):
    phi = d/N; best = np.inf
    for _ in range(starts):
        t = rng.uniform(0, 2*np.pi, N)
        for _ in range(steps):
            x = t - np.roll(t, -1) - phi
            g = sign*4*np.sin(x)                      # dE/dx for E = 4(1 - sign cos x)
            t -= lr*(g - np.roll(g, 1))
        x = t - np.roll(t, -1) - phi; best = min(best, np.sum(4*(1 - sign*np.cos(x))))
    return best
def floor(N, d):
    return min(4*N*(1 - np.cos((d - 2*np.pi*w)/N)) for w in range(-N-2, N+3))
worst = 0
for N in [3, 5, 6]:
    for d in np.linspace(0, 2*np.pi, 9):
        m, p = minimise(N, d, +1), minimise(N, d, -1)
        fm, fp = floor(N, d), floor(N, d + N*np.pi)
        worst = max(worst, abs(m - fm), abs(p - fp))
print(f'Claim A (floors by direct minimisation vs formula): max mismatch {worst:.1e}  {"PASS" if worst < 1e-6 else "KILL"}')
for N in [3, 5, 7, 4, 6]:
    ds = np.linspace(0, 2*np.pi, 4001)
    one = max(floor(N, d) for d in ds); both = max(min(floor(N, d), floor(N, d + N*np.pi)) for d in ds)
    print(f'N={N}: worst frustration, one book {one:.4f} (formula {4*N*(1-np.cos(np.pi/N)):.4f}); with both books {both:.4f} (odd-N prediction {4*N*(1-np.cos(np.pi/(2*N))):.4f})')
