## Symmetrized and polynomial size LP computing S^NS(MAC^N,k1,k2)  ##
## NB: a Mosek license is neeeded to run this program ##

from mosek.fusion import *
import math
import sys
sys.setrecursionlimit(10000)

#####   PARAMETERS   #####
## MAC and inputs/output sizes ##
# Here we have chosen the BAC channel. The meaning is MAC[y][x1][x2] := W(y|x1x2)

MAC = [[[1,0],[0,0]], [[0,1],[1,0]], [[0,0],[0,1]]]

Y = len(MAC)
X1 = len(MAC[0])
X2 = len(MAC[0][0])

## Number of messages and copies of the MAC ##
# Remark: ki should be at most Xi**N

N = 3
k1 = 4
k2 = 4

verbose = True # Switch to true if you want intermediate ans mosek updates

###  SMALL UTILITY FUNCTIONS  ###
# An orbit of Z^N is represented by the increasing list of its elements
def enumerateOrbits(Z,n,offset=0):
    # Enumerate increasing lists of {offset,...,Z-1+offset} of size n
    if n <= 0:
        raise Exception ('n should be a positive integer')
    elif n == 1:
        return [[i+offset] for i in range(Z)]
    else:
        liste = []
        for k in range(Z):
            liste = liste + [[k+offset]+l for l in enumerateOrbits(Z-k,n-1,k+offset)]
        return liste

def orbitSize(orb):
    # Compute the size of the orbit orb, so the size of {\sigma(orb), \sigma permutation}
    max_int = max(orb)
    prod = 1
    for i in range(max_int+1):
        prod = prod * math.factorial(orb.count(i))
    return math.factorial(len(orb)) / prod

def channel(wList):
    # Value of W(wList) = \prod_i W(y^i|x1^i x2^i), where wList = ((x1^i,x2^i,y^i))_i
    value = 1.
    for e in wList:
        x1 = e % X1
        x2 = (e/X1) % X2
        y = e/(X1*X2)
        value = value * MAC[y][x1][x2]
    return value

result = None

###  Orbits Lists and Indices  ###
if verbose:
    print("Generating the orbits lists...")
W = enumerateOrbits(X1*X2*Y,N)
U = enumerateOrbits(X1*X2,N)
U1 = enumerateOrbits(X1,N)
U2 = enumerateOrbits(X2,N)
V = enumerateOrbits(Y,N)
V1 = enumerateOrbits(X1*Y,N)
V2 = enumerateOrbits(X2*Y,N)
if verbose:
    print("...Done")

#####   LINEAR PROGRAM COMPUTING S^NS(MAC^N,k1k2)   #####
if verbose:
    print("Generating the linear program...")
with Model("S") as S:
    r = S.variable("r", [len(W)], Domain.greaterThan(0.0))
    r1 = S.variable("r1", [len(W)], Domain.greaterThan(0.0))
    r2 = S.variable("r2", [len(W)], Domain.greaterThan(0.0))
    p = S.variable("p", [len(U)], Domain.greaterThan(0.0))

    # Domain constraints
    for w in range(len(W)):
        wList = W[w] # Getting the orbit from its representative index
        w_X1X2List = [e % (X1*X2) for e in wList] # Projection on X1X2
        w_X1X2List.sort() # Recovering the orbit representative (the ordered list)
        w_X1X2 = U.index(w_X1X2List) # Getting the representative index of the orbit
        
        coeff = float(orbitSize(wList))/float(orbitSize(w_X1X2List))
        P = Expr.mul(coeff,p.index(w_X1X2))
        S.constraint(Expr.sub(r1.index(w),r.index(w)), Domain.greaterThan(0.0))
        S.constraint(Expr.sub(r2.index(w),r.index(w)), Domain.greaterThan(0.0))
        S.constraint(Expr.sub(P,r1.index(w)), Domain.greaterThan(0.0))
        S.constraint(Expr.sub(P,r2.index(w)), Domain.greaterThan(0.0))
        
        A = Expr.add(Expr.sub(P,Expr.add(r1.index(w),r2.index(w))),r.index(w))
        S.constraint(A, Domain.greaterThan(0.0))

    # Main constraints
    # \sum_{w:w_Y=v} r_w - |v| = 0
    for v in range(len(V)):
        vList = V[v] # Getting the orbit from its representative index
        A = Expr.constTerm(0.0)
        
        for w in range(len(W)):
            wList = W[w] # Getting the orbit from its representative index
            w_YList = [e / (X1*X2) for e in wList] # Projection on Y
            w_YList.sort() # Recovering the orbit representative (the ordered list)
            w_Y = V.index(w_YList) # Getting the representative index of the orbit
            
            if w_Y==v:
                A = Expr.add(A,r.index(w))
                
        A = Expr.sub(A,Expr.constTerm(orbitSize(vList)))
        S.constraint(A, Domain.equalsTo(0.0))

    # NS conditions
    # \sum_{w:w_X2Y=v2} r1_w - k1*\sum_{w:w_X2Y=v2} r_w = 0
    for v2 in range(len(V2)):
        v2List = V2[v2] # Getting the orbit from its representative index
        A = Expr.constTerm(0.0)
        B = Expr.constTerm(0.0)
        
        for w in range(len(W)):
            wList = W[w] # Getting the orbit from its representative index
            w_X2YList = [e / X1 for e in wList] # Projection on X2Y
            w_X2YList.sort() # Recovering the orbit representative (the ordered list)
            w_X2Y = V2.index(w_X2YList) # Getting the representative index of the orbit
            
            if w_X2Y==v2:
                A = Expr.add(A,r1.index(w))
                B = Expr.add(B,r.index(w))
                
        B = Expr.mul(k1,B)
        A = Expr.sub(A,B)
        S.constraint(A, Domain.equalsTo(0.0))

    # \sum_{w:w_X1Y=v1} r2_w - k2*\sum_{w:w_X1Y=v1} r_w = 0
    for v1 in range(len(V1)):
        v1List = V1[v1] # Getting the orbit from its representative index
        A = Expr.constTerm(0.0)
        B = Expr.constTerm(0.0)
        
        for w in range(len(W)):
            wList = W[w] # Getting the orbit from its representative index
            w_X1YList = [e % X1 + X1*(e/(X1*X2)) for e in wList] # Projection on X1Y
            w_X1YList.sort() # Recovering the orbit representative (the ordered list)
            w_X1Y = V1.index(w_X1YList) # Getting the representative index of the orbit
            
            if w_X1Y==v1:
                A = Expr.add(A,r2.index(w))
                B = Expr.add(B,r.index(w))
                
        B = Expr.mul(k2,B)
        A = Expr.sub(A,B)
        S.constraint(A, Domain.equalsTo(0.0))

    #\sum_{u:u_X2=v2_X2} p_u - k1*|v2_X2|/|v2|\sum_{w:w_X2Y=v2} r2_w = 0
    for v2 in range(len(V2)):
        v2List = V2[v2] # Getting the orbit from its representative index
        v2_X2List = [e % X2 for e in v2List] # Projection on X2 (from V2)
        v2_X2List.sort() # Recovering the orbit representative (the ordered list)
        v2_X2 = U2.index(v2_X2List) # Getting the representative index of the orbit

        A = Expr.constTerm(0.0)
        B = Expr.constTerm(0.0)

        for w in range(len(W)):
            wList = W[w] # Getting the orbit from its representative index
            w_X2YList = [e / X1 for e in wList] # Projection on X2Y
            w_X2YList.sort() # Recovering the orbit representative (the ordered list)
            w_X2Y = V2.index(w_X2YList) # Getting the representative index of the orbit
            
            if w_X2Y==v2:
                B = Expr.add(B,r2.index(w))
                
        coeff = float(k1)*float(orbitSize(v2_X2List))/float(orbitSize(v2List))
        B = Expr.mul(coeff,B)

        for u in range(len(U)):
            uList = U[u] # Getting the orbit from its representative index
            u_X2List = [e / X1 for e in uList] # Projection on X2 (from U)
            u_X2List.sort() # Recovering the orbit representative (the ordered list)
            u_X2 = U2.index(u_X2List) # Getting the representative index of the orbit
            
            if u_X2==v2_X2:
                A = Expr.add(A,p.index(u))

        A = Expr.sub(A,B)
        S.constraint(A, Domain.equalsTo(0.0))

    #\sum_{u:u_X1=v2_X1} p_u - k2*|v1_X1|/|v1|\sum_{w:w_X1Y=v1} r1_w = 0
    for v1 in range(len(V1)):
        v1List = V1[v1] # Getting the orbit from its representative index
        v1_X1List = [e % X1 for e in v1List] # Projection on X1 (from V1)
        v1_X1List.sort() # Recovering the orbit representative (the ordered list)
        v1_X1 = U1.index(v1_X1List) # Getting the representative index of the orbit
        
        A = Expr.constTerm(0.0)
        B = Expr.constTerm(0.0)

        for w in range(len(W)):
            wList = W[w] # Getting the orbit from its representative index
            w_X1YList = [e % X1 + X1*(e/(X1*X2)) for e in wList] # Projection on X1Y
            w_X1YList.sort() # Recovering the orbit representative (the ordered list)
            w_X1Y = V1.index(w_X1YList) # Getting the representative index of the orbit
            
            if w_X1Y==v1:
                B = Expr.add(B,r1.index(w))
                
        coeff = float(k2)*float(orbitSize(v1_X1List))/float(orbitSize(v1List))
        B = Expr.mul(coeff,B)

        for u in range(len(U)):
            uList = U[u] # Getting the orbit from its representative index
            u_X1List = [e % X1 for e in uList] # Projection sur X1 (depuis U)
            u_X1List.sort() # Recovering the orbit representative (the ordered list)
            u_X1 = U1.index(u_X1List) # Getting the representative index of the orbit
            
            if u_X1==v1_X1:
                A = Expr.add(A,p.index(u))

        A = Expr.sub(A,B)
        S.constraint(A, Domain.equalsTo(0.0))

    # Objectif
    Objectif = Expr.constTerm(0.0)

    for w in range(len(W)):
        wList = W[w] # Getting the orbit from its representative index
        value = channel(wList) # Getting the value of the channel on this input
        
        if value > 0.:
            Objectif = Expr.add(Objectif,Expr.mul(value,r.index(w)))
            
    Objectif = Expr.mul(1./float(k1*k2),Objectif)

    S.objective("obj", ObjectiveSense.Maximize, Objectif)

    if verbose:
        print("...Done")
    
    if verbose:
        S.setLogHandler(sys.stdout)
        S.setSolverParam("log",1)
        print("Mosek Log\n>>>>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<\n")

    # Resolution
    S.solve()
    result = S.primalObjValue()
    if verbose:
        print("\n>>>>>>>>>>>>>>>>>>>><<<<<<<<<<<<<<<<<<<<\n")
    
###  PRINTING  ###
print("For "+str(N)+" copies of the following MAC, where W(y|x1x2) is represented by MAC[y][x1][x2]:")
print(MAC)
print("we have that the best success probability with non-signaling assistance of sending "+str(k1)+" messages for sender 1 and "+str(k2)+" messages for sender 2 is equal to "+str(result))

