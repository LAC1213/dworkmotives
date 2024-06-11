This program is a supplement to the paper "Dwork Motives, Monodromy and Potential Automorphy". There are various functions for checking properties of hypergeometric parameters such as Hodge--Tate weights, big monodromy and whether the determinant is an nth power. Property (R) is implemented as `is_regular`, (BM) is `has_big_monodromy`, (BM_fin) is `has_big_monodromy_finite`, (D) is `det_nth_power`. 

The algorithm described in section 4 of the paper is implemented in the function `find_params(d,p)`. For example if we run

    >>> find_params(18, [3,1])
    [(18, 1, 7, 10, (0, 0, 0, 3), (4, 11, 16, 17))]

we recover one row of table 2.
