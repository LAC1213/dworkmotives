import math
import itertools
import sympy
from fractions import Fraction

# input: 
#   d : positive integer
#   alphas : list/tuple of integers
#   betas : list/tuple of integers
# output:
#   True/False depending if (alphas, betas) is a hypergeometric parameter
def is_param(d, alphas, betas):
    if len(alphas) != len(betas):
        return False
    if len(set([b % d for b in betas])) < len(betas):
        return False
    for a in alphas:
        if (a % d) in [b % d for b in betas]:
            return False
    return (sum( alphas) - sum(betas) - (d * (d-1))//2) % d == 0

###########################
### Hodge--Tate weights ###
###########################

# input: a hypergeometric parameter
# ouput:
#   a list of length phi(d) such that the ith entry 
#   is the tuple of Hodge--Tate weights of M(s*alphas, s*betas)_{dR}
#   and s is the ith positive integer which is coprime to d
def hodge_tate_weights(d, alphas, betas):
    weights = []
    n = len(betas)
    for s in range(1,d,1):
        if math.gcd(s,d) == 1:
            ws = []
            for i in range(0,n,1):
                l = list(range(0,d))
                for b in betas:
                    l.remove((-s*b)%d )
                l = l + [(-s*a) % d for a in alphas]
                w = sum([(s*betas[i] + x) % d for x in l])
                ws.append(int((w - d)/d))
            ws.sort()
            weights.append(tuple(ws))
    return weights

# input: a hypergeometric parameter
# ouput: True if at every embedding the Hodge numbers are <= 1. False otherwise
def is_regular(d, alphas, betas):
    n = len(alphas)
    return all([n == len(set(w)) for w in hodge_tate_weights(d, alphas, betas)])

# input:
#   d : positive integer
#   c1 : integer
#   c2 : integer
# output:
#   a list of integers representing the labelled Hodge--Tate weights 
#   of the Hecke character J_(c_1, c_2)
def jacobi_weights(d, c1, c2):
    c0 = (- c1 - c2) % d
    weights = []
    for s in range(1,d,1):
        if math.gcd(s,d) == 1:
            w = -d + (s*c0 % d) + (s*c1 % d) + (s*c2 % d)
            if c1 == 0 and c2 == 0:
                w = 0
            weights.append(int(w/d))
    return weights

# input: 
#   c1, c2 : integers
#   d, alphas, betas : hypergeometric parameter
# output: 
#   the Hodge--Tate weights weights of the determinant 
#   of M(alphas, betas) \otimes J_(c_1,c_2)
def twist_weights(d, c1, c2, alphas, betas):
    jws = jacobi_weights(d,c1,c2)
    hws = hodge_tate_weights(d,alphas,betas)
    n = len(alphas)
    weights = []
    for x in zip(jws, hws):
        weights.append(sum(x[1]) + n*x[0])
    return weights

##################################
### monodromy group properties ###
##################################

# input: hypergeometric parameter
# output: True if there is no non trivial additive shift, no hermitian 
#         form, and betas are not an arithmetic progression
def has_big_monodromy(d, alphas_tup, betas_tup):
    alphas = list(alphas_tup)
    betas = list(betas_tup)
    alphas.sort()
    betas.sort()

    #alphas not pairwise distinct   
    if len(set(alphas)) == len(alphas):
        return False

    #betas are not arithmetic progression
    bs = betas + [betas[0]]
    arithmetic_prog = True
    for i in range(1, len(betas), 1):
        if (bs[i + 1] - bs[i]) % d != (bs[1] - bs[0]) % d:
            arithmetic_prog = False
    if arithmetic_prog:
        return False

    #no additive shift or hermitian form
    n = len(alphas)
    shift_alphas = alphas.copy()
    shift_betas = betas.copy()
    for t in range(0, d, 1):
        for i in range(0,n,1):
            shift_alphas[i] = (alphas[i] + t) % d
            shift_betas[i] = (betas[i] + t) % d
        shift_alphas.sort()
        shift_betas.sort()
        if alphas == shift_alphas and betas == shift_betas and t != 0:
            return False
        neg_alphas = shift_alphas.copy()
        neg_betas = shift_betas.copy()
        for i in range(0, n, 1):
            neg_alphas[i] = -neg_alphas[i]
            neg_betas[i] = - neg_betas[i]
        neg_alphas.sort()
        neg_betas.sort()
        if neg_alphas == shift_alphas and neg_betas == shift_betas:
            return False
    return True

# returns V < (Z/dZ)* which corresponds to U = {1, -1}
def standard_v(d):
    return list(filter(lambda x : math.gcd(d,x) == 1, range(1, math.ceil(d/2), 1)))

# input: 
#   d, alphas, betas : hypergeometric parameter
#   v_group : list of integers representing a subgroup V of (Z/dZ)*
# output: True if for each v in V we have
#         {v a_i - v a_j } != {a_i - a_j}
#         or {v b_i - v b_j} != {b_i - b_j}
def has_big_monodromy_finite(d, v_group, alphas, betas):
    malphas = sum([[(a - b) % d for a in alphas ] for b in alphas], [])
    mbetas = sum([[(a - b) % d for a in betas] for b in betas], [])
    malphas.sort()
    mbetas.sort()
    salphas = malphas.copy()
    sbetas = mbetas.copy()
    for s1 in v_group:
        if s1 == 1:
            continue
        for i in range(0,len(malphas),1):
            salphas[i] = s1*malphas[i] % d
            sbetas[i] = s1*mbetas[i] % d
        salphas.sort()
        sbetas.sort()
        if salphas == malphas and sbetas == mbetas:
            return False
    return True

##############################
### determinant properties ###
##############################

# input: positive integer d
# output: list of lists representing the functions in the set E(d)
def epsilon_functions(d):
    epsilons = []
    zero_function = (d-1) * [0]
    for a in range(1, int(d/2) + 1):
        new_epsilon = zero_function.copy()
        new_epsilon[a - 1] += 1
        new_epsilon[d - 1 - a] += 1
        epsilons.append((1, a, new_epsilon))
    for p in sympy.primerange(1,d):
        if d % p == 0:
            for a in range(1, int(d/p)):
                if p*a % d != 0:
                    new_epsilon = zero_function.copy()
                    new_epsilon[d - p*a - 1] += 1
                    for b in range(0, p):
                        new_epsilon[a + b*int(d/p) - 1] += 1
                    epsilons.append((p, a, new_epsilon))
    return epsilons

# input: 
#   d, alphas, betas : hypergeometric parameter
#   c1, c2 : integers
# output:
#   list of coefficients x_epsilon
def epsilon_coeffs(d, c1, c2, alphas, betas):
    l = list(range(0,d))
    for b in betas:
        l.remove( (-b)%d)
    l = l + [(-a) % d for a in alphas]
    
    w = sum([[(x + b) % d for x in l] for b in betas], [])
    
    if c1 != 0 and c2 != 0 and (c1 + c2) % d != 0:
        w = w + len(alphas) * [c1, c2, (-c1 - c2) % d]
    w.sort()

    f = (d-1)*[0]
    for el, it in itertools.groupby(w):
        f[el - 1] = len(list(it))
    # f[x - 1] = n + \sum_{i,j} \delta_{\beta_j - \alpha_i}(x) - \sum_{i,j} \delta_{\beta_j - \beta_i} + n \sum_{i = 0}^2 \delta_{c_i}

    epsilons = epsilon_functions(d)
    epsilon_vectors = list(map(lambda x : x[2], epsilons))
    independent_epsilons = sympy.Matrix(epsilon_vectors).transpose().columnspace()
    A = sympy.Matrix([list(f) for f in independent_epsilons]).transpose()
    return list(A.solve(sympy.Matrix(f)))


# input:
#   d, alphas, betas : hypergeometric parameter
#   c1, c2 : integers
# output:
#   list of tuples (p, y_p), where y_p is a fraction.
def gamma_exponents(d, c1, c2, alphas, betas):
    l = list(range(0,d))
    for b in betas:
        l.remove( (-b)%d)
    l = l + [(-a) % d for a in alphas]
    
    w = sum([[(x + b) % d for x in l] for b in betas], [])
    
    if c1 != 0 and c2 != 0 and (c1 + c2) % d != 0:
        w = w + len(alphas) * [c1, c2, (-c1 - c2) % d]
    w.sort()

    f = (d-1)*[0]
    for el, it in itertools.groupby(w):
        f[el - 1] = len(list(it))

    epsilons = epsilon_functions(d)
    epsilon_vectors = list(map(lambda x : x[2], epsilons))
    independent_epsilons = sympy.Matrix(epsilon_vectors).transpose().columnspace()
    A = sympy.Matrix([list(f) for f in independent_epsilons]).transpose()
    coeffs = A.solve(sympy.Matrix(f))

    exponents = []
    for p in sympy.primerange(1,d):
        if d % p == 0:
            exponent = 0
            for k, a, ep in epsilons:
                if k == p:
                    exponent += (Fraction(1,2)-Fraction(a,d))*sum([Fraction(coeffs[i]) for i in range(len(independent_epsilons)) if list(independent_epsilons[i]) == ep])
            exponents.append((p, exponent))
    exponent = 0
    for k, a, ep in epsilons:
        if k == 1:
            exponent += Fraction(a,d)* sum([coeffs[i] for i in range(len(independent_epsilons)) if list(independent_epsilons[i]) == ep])
        else:
            exponent += (Fraction(k*a,d) + Fraction((k - 1),4))* sum([Fraction(coeffs[i]) for i in range(len(independent_epsilons)) if list(independent_epsilons[i]) == ep])
    exponents.append((1, exponent))
    return exponents

# input:
#   d, alphas, betas : hypergeometric parameter
#   c1, c2 : integers
# ouput:
#   if this return True then the determinant of M(alphas, betas) is an nth power times chi_cyc^(-n(n-1)/2)
def det_nth_power(d, c1, c2, alphas, betas):
    if len(set(twist_weights(d, c1, c2, alphas, betas))) > 1:
        return False
    
    if not is_regular(d, alphas, betas):
        return False

    n = len(alphas)
    for s in range(1, d, 1):
        if math.gcd(s,d) == 1:
            if sum([ sum([(s*b - s*a) % d for b in betas]) for a in alphas]) != n* sum([(s * betas[i] - s * alphas[i]) % d for i in range(0,n,1)]):
                return False
    
    x_epsilon = epsilon_coeffs(d, c1, c2, alphas, betas)
    if not all([x.denominator == 1 for x in x_epsilon]):
        return False

    exponents = gamma_exponents(d, c1, c2, alphas, betas)
    for p, e in exponents:
        if p > 1 and (d  % 4 == 0 or p % 4 == 1):
            e = 2*e
        if math.gcd(e.denominator, n) != 1 and p > 1:
            return False
        if p == 1 and math.gcd(n, sympy.totient(math.lcm(2*e.denominator, d))//sympy.totient(d)) != 1:
            return False
    return True

##################################
### finding special parameters ###
##################################

# input: hypergeometric parameter
# output: returns True if the parameter satisfied (BM), (R), (BM_fin) (for U = {+-1})
def is_special(d, alphas, betas, BM_finite = False):
    alphas_copy = alphas
    betas_copy = betas

    if not is_regular(d, alphas_copy, betas_copy):
        return False

    if not has_big_monodromy(d, alphas_copy, betas_copy):
        return False

    if BM_finite:
        if not has_big_monodromy_finite(d, standard_v(d), alphas_copy, betas_copy):
            return False

    return True

# input:
#   d : positive integer
#   partition : a list representing a partition
# output:
#   a list of hypergeometric parameters of dimension n modulo d satisfying
#   (BM), (BM_fin), (R), (UM), (D)
def find_params(d, partition, BM_finite = False, find_all = False, determinant = True):
    result = []
    n = sum(partition)
    for vs in itertools.combinations(range(1,d), n + len(partition) - 2):
        betas = vs[len(partition) - 1:]
        alphas = partition[0]*(0,)
        for j, p in enumerate(partition):
            if j > 0:
                alphas = alphas + p * (vs[j - 1],)
        lastbeta = (int(d*(d-1)/2) + sum(alphas) - sum(betas)) % d
        if lastbeta in vs or lastbeta == 0:
            continue
        else:
            betas = betas + (lastbeta,)

        if is_special(d, alphas, betas, BM_finite):
            if not determinant:
                result.append((d,0,0,0,alphas, betas))
                if not find_all:
                    return result
            else:
                searching_twist = True
                for c1 in range(0,d,1):
                    if not searching_twist:
                        break
                    for c2 in range(c1,d,1):
                        if not searching_twist:
                            break
                        if ((c1 + c2) % d != 0 and c1 != 0) or (c1 == 0 and c2 == 0):
                            if det_nth_power(d, c1, c2, alphas, betas):
                                searching_twist = False
                                result.append((d, c1, c2, (-c1 - c2) % d, alphas, betas))
                                if not find_all:
                                    return result #only return first hit (otherwise very very slow)
    return result

                       

def partitions(n, I=1):
    yield [n,]
    for i in range(I, n//2 + 1):
        for p in partitions(n-i, i):
            yield [i,] + p

#returns list of partitions of n excluding [1,1,...,1] and [2,1,1,...,1].
def partition_lists(n):
    result = []
    ps = list(partitions(n))
    ps.sort()
    ps.reverse()
    for p in ps:
        p.sort()
        p.reverse()
        result.append(p)
    result.pop()
    result.pop()
    return result

def list_no_bracket(l):
    s = ""
    for x in l:
        s += str(x)
        s += ", "
    return s[:-2]

def latex_param(p):
    return "$" + str(len(p[4])) + "$ & $" + str(p[0]) + "$ & $" + list_no_bracket(p[4]) + "$ & $" + list_no_bracket(p[5]) + "$ & $" + list_no_bracket(p[1:4]) + "$ & $ \\{\\pm 1\\} $ \\\\"
                            
def print_params_latex(ns, ds):
    ps = sum([partition_lists(n) for n in ns], [])
    for d in ds:
        for p in ps:
            for x in find_params(d,p):
                print(latex_param(x))
     