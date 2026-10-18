"""Numerical sanity checks of the claims in 'Non-normality is connection energy' (v7)."""
import numpy as np, itertools
rng = np.random.default_rng(20261018)
def herm(r): X = rng.normal(size=(r,r))+1j*rng.normal(size=(r,r)); return (X+X.conj().T)/2
def unit(r): Q,R = np.linalg.qr(rng.normal(size=(r,r))+1j*rng.normal(size=(r,r))); return Q*(np.diag(R)/abs(np.diag(R)))
def build(n,r,E,D,Aed):
    H=np.zeros((n*r,n*r),complex)
    for i in range(n): H[i*r:(i+1)*r,i*r:(i+1)*r]=D[i]
    for (i,j),U in Aed.items():
        H[i*r:(i+1)*r,j*r:(j+1)*r]+=U; H[j*r:(j+1)*r,i*r:(i+1)*r]+=-U.conj().T
    return H
fro2=lambda X: np.sum(abs(X)**2)
worst=0
for trial in range(300):
    n=rng.integers(2,7); r=rng.integers(1,5)
    E=[e for e in itertools.combinations(range(n),2) if rng.random()<0.5]
    D=[herm(r) for _ in range(n)]; Aed={e:unit(r) for e in E}
    H=build(n,r,E,D,Aed); C=H@H.conj().T-H.conj().T@H
    rhs=sum(fro2(D[i]-U@D[j]@U.conj().T) for (i,j),U in Aed.items())
    worst=max(worst,abs(fro2(C)/8-rhs)/(1+rhs))
print("identity (1) worst rel. error over 300 random graphs:",worst)
# (2): parallel D => normal
n,r=4,3; E=[(0,1),(1,2),(2,3),(3,0)]; Aed={e:unit(r) for e in E}
X=herm(r)
# Hermitian part requirement: drop D_i = D_i^* and (1) fails
D=[herm(r)+1j*np.eye(r)*0 for _ in range(n)]
Dn=[herm(r)+0.3j*herm(r) for _ in range(n)]  # non-Hermitian blocks
H=build(n,r,E,Dn,Aed); C=H@H.conj().T-H.conj().T@H
rhs=sum(fro2(Dn[i]-U@Dn[j]@U.conj().T) for (i,j),U in Aed.items())
print("non-Hermitian D: lhs/8 =",fro2(C)/8," rhs =",rhs,"(should differ)")
# non-unitary edges: (1) fails but the general form 4*sum|D_iA-AD_j|^2 holds
Aed2={e:2*unit(r) for e in E}; H=build(n,r,E,D,Aed2); C=H@H.conj().T-H.conj().T@H
rhs=sum(fro2(D[i]-U@D[j]@np.linalg.inv(U)) for (i,j),U in Aed2.items())
gen=sum(fro2(D[i]@U-U@D[j]) for (i,j),U in Aed2.items())
print("scaled-unitary edges: lhs/8=",fro2(C)/8," paper rhs(using A^{-1})=",rhs," sum||D_iA-AD_j||^2=",gen)
# scalar case r=1, weighted: |a_ij|^2 |d_i-d_j|^2
n=5;E=[(0,1),(1,2),(2,3),(3,4),(0,4),(1,3)]
d=rng.normal(size=n); a={e:rng.normal()+1j*rng.normal() for e in E}
H=np.diag(d).astype(complex)
for (i,j),w in a.items(): H[i,j]=w; H[j,i]=-np.conj(w)
C=H@H.conj().T-H.conj().T@H
print("scalar weighted Dirichlet: lhs/8=",fro2(C)/8," sum|a|^2|di-dj|^2=",sum(abs(w)**2*(d[i]-d[j])**2 for (i,j),w in a.items()))
# (3) holonomy: cycle, X commuting with loop holonomy -> parallel section exists, H normal
n,r=4,2; E=[(1,0),(2,1),(3,2),(0,3)]  # transport i<-j by A_ij, edge (i,j) stored as A_ij
Aed={e:unit(r) for e in E}
W=Aed[(0,3)]@Aed[(3,2)]@Aed[(2,1)]@Aed[(1,0)]
w,V=np.linalg.eig(W); P=V[:,[0]]; X=(P@P.conj().T); X=(X+X.conj().T)/2  # spectral projector of W: commutes
D=[X]; 
for (i,j) in [(1,0),(2,1),(3,2)]: D.append(Aed[(i,j)]@D[j]@Aed[(i,j)].conj().T)
H=build(n,r,E,D,Aed); C=H@H.conj().T-H.conj().T@H
print("holonomy-fixed X gives normal H: ||[H,H*]||_F =",np.sqrt(fro2(C)), " [X,W] =",np.linalg.norm(X@W-W@X))
Y=herm(r); D=[Y]
for (i,j) in [(1,0),(2,1),(3,2)]: D.append(Aed[(i,j)]@D[j]@Aed[(i,j)].conj().T)
H=build(n,r,E,D,Aed); C=H@H.conj().T-H.conj().T@H
print("generic Y (not fixed): ||[H,H*]||_F =",np.sqrt(fro2(C)), " ||[Y,W]|| =",np.linalg.norm(Y@W-W@Y))
# dimension count: dim ker = dim of commutant of holonomy in Herm(r)
