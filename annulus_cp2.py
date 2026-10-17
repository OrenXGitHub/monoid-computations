#!/usr/bin/env python3
"""
annulus_cp2.py -- a 122-element monoid M with BM ~ CP^2, and its cohomology ring mod 2, 3, 5, 7.

Let L0 = {1} u {x_kj : k,j in {0,1}},  x_kj x_k'j' = x_kj'   (B L0 = S^2).
Let A~ be the simplicial complex on the integers whose simplices are the sets of at most three consecutive integers
(a triangulated strip), A = A~/(n ~ n+2) an annulus with two triangles, and C = (line with edges {c,c+1})/(c ~ c+1) a circle.
    i_k : C -> A,  c |-> 2c + k            (the two boundary circles)
    r_j : A -> C,  n |-> floor((n+j)/2)    (two retractions whose chosen lifts have the defect r_1 i_1 = deck shift)
L0 acts on A by x_kj = i_k r_j.  With O_3 = End_Delta([2]),

    M  =  (L0 x O_3^op)   u   ( A_2 x {r_0,r_1} x {0,1,2} )            (50 + 12*6 = 122 elements)

    (p,r,i)(p',r',i') = (p,r',i'),   (x,theta).(p,r,i) = (x.theta^*p, r, i),   (p,r_j,i).(x,theta) = (p, r_j x, theta(i)),
    with r_j.1 = r_j and r_j.x_kj' = r_j'.

Requires numpy.
"""

import numpy as np, itertools, sys

class LinSpan:
    """incremental echelon basis mod p"""
    def __init__(self, n, p):
        self.n, self.p, self.rows, self.piv = n, p, {}, []
    def reduce(self, v):
        v = v % self.p
        for c in self.piv:
            if v[c]:
                v = (v - v[c] * self.rows[c]) % self.p
        return v
    def add(self, v):
        v = self.reduce(v.copy())
        nz = np.nonzero(v)[0]
        if len(nz) == 0: return False
        c = int(nz[0]); v = (v * pow(int(v[c]), -1, self.p)) % self.p
        for c2 in self.piv:
            r = self.rows[c2]
            if r[c]: self.rows[c2] = (r - r[c] * v) % self.p
        self.rows[c] = v; self.piv.append(c); self.piv.sort()
        return True
    def dim(self): return len(self.piv)

def rref(A, p):
    A = A.copy() % p; m, n = A.shape; piv = []; r = 0
    for c in range(n):
        if r >= m: break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0: continue
        k = r + nz[0]
        if k != r: A[[r, k]] = A[[k, r]]
        A[r] = (A[r] * pow(int(A[r, c]), -1, p)) % p
        col = A[:, c].copy(); col[r] = 0
        A = (A - np.outer(col, A[r])) % p
        piv.append(c); r += 1
    return A, piv

def nullspace(A, p):
    m, n = A.shape
    R, piv = rref(A, p)
    free = [c for c in range(n) if c not in piv]
    N = np.zeros((len(free), n), dtype=np.int64)
    for i, f in enumerate(free):
        N[i, f] = 1
        for r, c in enumerate(piv): N[i, c] = (-R[r, f]) % p
    return N

def solve(A, b, p):
    """one solution x of A x = b mod p (assumes consistent)"""
    m, n = A.shape
    R, piv = rref(np.hstack([A, b.reshape(-1, 1)]), p)
    assert n not in piv, "inconsistent system"
    x = np.zeros(n, dtype=np.int64)
    for r, c in enumerate(piv): x[c] = R[r, n]
    return x

class Monoid:
    def __init__(self, mul, one=0):
        self.mul = np.array(mul, dtype=np.int64); self.n = len(mul); self.one = one
        n = self.n
        self.idem = [a for a in range(n) if self.mul[a, a] == a]
        self.Mf = {f: sorted(set(int(self.mul[x, f]) for x in range(n))) for f in self.idem}
        self.idem.sort(key=lambda f: len(self.Mf[f]))
    def check(self):
        m = self.mul; n = self.n
        ok = all(m[self.one, a] == a and m[a, self.one] == a for a in range(n))
        A = m[m, :]            # (ab)c
        B = m[:, m]            # a(bc)
        return ok and np.array_equal(A, B)
    def lmul(self, a, v, r):
        """a . v for v in (kM)^r"""
        n = self.n; out = np.zeros_like(v)
        V = v.reshape(r, n); O = out.reshape(r, n)
        for i in range(r): np.add.at(O[i], self.mul[a], V[i])
        return out

class Resolution:
    def __init__(self, M, p, maxdeg, verbose=False):
        self.M, self.p = M, p
        n = M.n
        e0 = M.idem[0]
        self.idems = [[e0]]          # idempotents of generators of P_k
        self.W = [None]              # W[k][j] = d(gen_j) in ambient (kM)^{rank_{k-1}}
        self.Dmat = [None]
        for k in range(1, maxdeg + 1):
            self._extend(k)
            if verbose: print("deg", k, "rank", len(self.idems[k]), file=sys.stderr)
            if len(self.idems[k]) == 0: break
        self.top = len(self.idems) - 1
    def basis(self, k):
        return [(j, x) for j, f in enumerate(self.idems[k]) for x in self.M.Mf[f]]
    def _matrix(self, k):
        """matrix of d_k : P_k -> ambient P_{k-1} in basis coords of P_k (k>=1); k=0: augmentation"""
        M, p = self.M, self.p; n = M.n
        B = self.basis(k)
        if k == 0:
            return np.ones((1, len(B)), dtype=np.int64)
        r = len(self.idems[k - 1])
        D = np.zeros((r * n, len(B)), dtype=np.int64)
        for c, (j, x) in enumerate(B):
            D[:, c] = M.lmul(x, self.W[k][j], r) % p
        return D
    def _extend(self, k):
        M, p = self.M, self.p; n = M.n
        D = self._matrix(k - 1)
        if k - 1 >= 1: self.Dmat[k - 1] = D
        else: self.Dmat[0] = D
        B = self.basis(k - 1); r = len(self.idems[k - 1])
        N = nullspace(D, p)
        ker = np.zeros((N.shape[0], r * n), dtype=np.int64)
        for c, (j, x) in enumerate(B): ker[:, j * n + x] = N[:, c]
        S = LinSpan(r * n, p); gens = []; fs = []; target = ker.shape[0]
        for f in M.idem:
            if S.dim() >= target: break
            for v in ker:
                if S.dim() >= target: break
                w = M.lmul(f, v, r) % p
                if not w.any(): continue
                if np.any(S.reduce(w.copy())):
                    gens.append(w); fs.append(f)
                    for x in M.Mf[f]: S.add(M.lmul(x, w, r) % p)
        assert S.dim() == target
        # prune redundant generators (backward pass)
        keep = list(range(len(gens)))
        for i in reversed(range(len(gens))):
            T = LinSpan(r * n, p)
            for j in keep:
                if j == i: continue
                for x in M.Mf[fs[j]]: T.add(M.lmul(x, gens[j], r) % p)
            if T.dim() == target: keep.remove(i)
        self.idems.append([fs[i] for i in keep]); self.W.append([gens[i] for i in keep]); self.Dmat.append(None)
    def aug(self, k):
        """A_k[j,i] = augmentation of component i of d(gen_j of P_k)"""
        n = self.M.n; r = len(self.idems[k - 1])
        return np.array([w.reshape(r, n).sum(axis=1) % self.p for w in self.W[k]], dtype=np.int64).reshape(len(self.W[k]), r)
    def cohomology(self, k):
        """returns (cocycle basis reps of H^k, coboundary span) ; need k < top"""
        p = self.p; rk = len(self.idems[k])
        if rk == 0: return [], LinSpan(0, p)
        Z = nullspace(self.aug(k + 1), p) if (k + 1 <= self.top and len(self.idems[k + 1])) else np.eye(rk, dtype=np.int64)
        Bd = LinSpan(rk, p)
        if k >= 1:
            A = self.aug(k)
            for i in range(A.shape[1]): Bd.add(A[:, i].copy())
        reps = []; S = LinSpan(rk, p)
        for row in list(Bd.rows.values()): S.add(row.copy())
        for z in Z:
            if S.add(z.copy()): reps.append(z % p)
        return reps, Bd
    def betti(self, upto):
        return [len(self.cohomology(k)[0]) for k in range(0, upto + 1)]
    def apply(self, images, v, k, rt):
        """chain map component: v in ambient P_k, images[j] in ambient of rank rt; returns sum c_{j,x} x.images[j]"""
        M, p = self.M, self.p; n = M.n
        out = np.zeros(rt * n, dtype=np.int64)
        V = v.reshape(len(self.idems[k]), n)
        for j in range(V.shape[0]):
            for x in np.nonzero(V[j])[0]:
                out = (out + V[j, x] * M.lmul(int(x), images[j], rt)) % p
        return out
    def lift(self, phi, a, m):
        """phi cocycle on P_a; returns chain maps F[i]: P_{a+i} -> P_i for i=0..m (list of image lists)"""
        M, p = self.M, self.p; n = M.n; e0 = self.idems[0][0]
        F = []
        im0 = []
        for j, f in enumerate(self.idems[a]):
            v = np.zeros(n, dtype=np.int64); v[M.mul[f, e0]] = phi[j] % p; im0.append(v)
        F.append(im0)
        for i in range(1, m + 1):
            ri = len(self.idems[i]); rprev = len(self.idems[i - 1])
            D = self.Dmat[i] if self.Dmat[i] is not None else self._matrix(i)
            Bi = self.basis(i); ims = []
            for g, f in enumerate(self.idems[a + i]):
                t = self.apply(F[i - 1], self.W[a + i][g], a + i - 1, rprev)
                xs = solve(D, t, p)
                s = np.zeros(ri * n, dtype=np.int64)
                for c, (j, x) in enumerate(Bi): s[j * n + x] = xs[c]
                ims.append(M.lmul(f, s, ri) % p)
            F.append(ims)
        return F
    def product(self, psi, m, phi, a):
        """Yoneda product psi (deg m) . phi (deg a) as cochain on P_{a+m}"""
        n = self.M.n; F = self.lift(phi, a, m); rm = len(self.idems[m])
        out = []
        for g in range(len(self.idems[a + m])):
            comp = F[m][g].reshape(rm, n).sum(axis=1) % self.p
            out.append(int(np.dot(comp, psi) % self.p))
        return np.array(out, dtype=np.int64)
    def is_coboundary(self, c, k):
        _, Bd = self.cohomology(k)
        return not np.any(Bd.reduce(c.copy()))

def report(name, mul, p=2, maxdeg=7, prods=True):
    M = Monoid(mul); assert M.check(), "not a monoid"
    R = Resolution(M, p, maxdeg)
    top = R.top - 1
    H = {k: R.cohomology(k)[0] for k in range(0, top + 1)}
    print(f"{name}: |M|={M.n} p={p} betti(0..{top})={[len(H[k]) for k in range(top+1)]}")
    found = False
    if prods:
        for a in range(1, top + 1):
            for b in range(a, top + 1):
                if a + b > top: continue
                for phi in H[a]:
                    for psi in H[b]:
                        c = R.product(psi, b, phi, a)
                        if not R.is_coboundary(c, a + b):
                            found = True; print(f"   NONZERO product H^{a} x H^{b} -> H^{a+b}")
        if not found: print("   all products of positive-degree classes vanish (in computed range)")
    return R

# ------------------------------------------------------------------ the annulus monoid
L0=[[0]*5 for _ in range(5)]
for a in range(5): L0[0][a]=a; L0[a][0]=a
for k,j,k2,j2 in itertools.product(range(2),repeat=4): L0[1+2*k+j][1+2*k2+j2]=1+2*k+j2
def norm(s):
    sh=(s[0]//2)*2; return tuple(n-sh for n in s)
A2=sorted({norm((a,a+d1,a+d2)) for a in (0,1) for d1,d2 in ((0,0),(0,1),(0,2),(1,1),(1,2),(2,2))})
O3=[t for t in itertools.product(range(3),repeat=3) if t[0]<=t[1]<=t[2]]
def actL(x,s):
    if x==0: return s
    k,j=divmod(x-1,2)
    return norm(tuple(2*((n+j)//2)+k for n in s))
els=[('n',0,(0,1,2))]+[('n',x,th) for x in range(5) for th in O3 if (x,th)!=(0,(0,1,2))]+[('k',p,j,i) for p in A2 for j in (0,1) for i in range(3)]
def mult(a,b):
    if a[0]=='n' and b[0]=='n': return ('n',L0[a[1]][b[1]],tuple(b[2][a[2][t]] for t in range(3)))
    if a[0]=='n':
        _,x,th=a; _,p,j,i=b
        return ('k',actL(x,norm(tuple(p[th[t]] for t in range(3)))),j,i)
    if b[0]=='n':
        _,p,j,i=a; _,x,th=b
        return ('k',p,(j if x==0 else (x-1)%2),th[i])
    return ('k',a[1],b[2],b[3])
idx={e:k for k,e in enumerate(els)}
mul=[[idx[mult(a,b)] for b in els] for a in els]
if __name__=="__main__":
    assert all(actL(L0[x][y],p)==actL(x,actL(y,p)) for x in range(5) for y in range(5) for p in A2), "L0 does not act"
    print("|M| =",len(mul),"  associative and unital:",Monoid(mul).check())
    for p in (2,3,5,7):
        report("M_annulus",mul,p=p,maxdeg=8)
