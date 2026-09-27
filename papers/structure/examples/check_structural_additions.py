"""Exact-rational checks of added manuscript identities; no lab dependencies.
Expressions are finite sums c*x^p*exp(-b*x), with rational c and b.
These checks complement the proofs; they do not prove stochastic existence.
"""
from fractions import Fraction as F
from pathlib import Path
import json
from math import factorial


def term(p=0,b=0,c=1):return {(p,F(b)):F(c)} if c else {}
def add(*xs):
    result={}
    for x in xs:
        for k,v in x.items():result[k]=result.get(k,F(0))+v
    return {k:v for k,v in result.items() if v}
def scale(x,c):return {k:v*c for k,v in x.items() if v*c}
def mul(x,y):
    return add(*(term(p+q,b+d,c*e) for (p,b),c in x.items() for (q,d),e in y.items()))
def derivative(x):
    return add(*(add(term(p-1,b,c*p) if p else {},term(p,b,-b*c)) for (p,b),c in x.items()))
def integral(x):
    # Definite integral from zero; integrate each polynomial-exponential term.
    result={}
    for (p,b),c in x.items():
        if not b:piece=term(p+1,0,c/F(p+1))
        else:
            piece=term(0,0,c*F(factorial(p))/b**(p+1))
            for j in range(p+1):piece=add(piece,term(j,b,-c*F(factorial(p),factorial(j))/b**(p-j+1)))
        result=add(result,piece)
    return result


def check_svensson(beta,level_var,cov):
    z=[F(1),F(-2),F(3),F(2)/beta]
    phi=[term(),term(0,beta),term(1,beta),term(1,2*beta)]
    Q=[[F(0) for _ in range(4)] for _ in range(4)]
    Q[0][0]=level_var;Q[0][1]=Q[1][0]=cov;Q[1][1]=beta*z[3]
    assert Q[0][0]*Q[1][1]>=cov*cov
    mu=[F(0),z[2]+z[3]-beta*z[1]-cov/beta,cov-beta*z[2],-2*beta*z[3]]
    actual=add(*(scale(phi[i],mu[i]) for i in range(4)),
               scale(derivative(add(*(scale(phi[i],z[i]) for i in range(4)))),-1),
               *(scale(mul(phi[i],integral(phi[j])),-Q[i][j]) for i in range(4) for j in range(4)))
    expected=add(term(c=-cov/beta),term(1,c=-level_var))
    assert actual==expected


def check_variance(kappa,v):
    e1,e2,e4=[term(0,j*kappa) for j in [1,2,4]]
    actual=add(scale(e1,1/kappa),scale(e2,(v-2)/(2*kappa)),scale(e4,-v/(2*kappa)))
    required=add(mul(e1,integral(e1)),scale(mul(e2,integral(e2)),v))
    assert actual==required
    a1,a2=integral(e1),integral(e2)
    assert integral(actual)==scale(add(mul(a1,a1),scale(mul(a2,a2),v)),F(1,2))
    assert 1/kappa+(v-2)/(2*kappa)-v/(2*kappa)==0


def main():
    for beta in [F(1,2),F(1),F(3)]:
        check_svensson(beta,F(3),F(1));check_svensson(beta,F(0),F(0))
        for v in [F(3,2),F(2),F(5,2)]:check_variance(beta,v)
    mat=[[F(1),F(1),F(1)],[F(1,2),F(1,4),F(1,16)],[F(1,4),F(1,16),F(1,256)]]
    a,b,c=mat[0];d,e,f=mat[1];g,h,i=mat[2]
    determinant=a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)
    assert determinant==F(-21,1024)
    result=dict(arithmetic='exact rational polynomial-exponential coefficients',
                svensson_cases=6,variance_hjm_and_bond_cases=9,
                curve_recovery_determinant=str(determinant),passed=True)
    path=Path(__file__).with_name('structural_additions_checks.json')
    path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':main()
