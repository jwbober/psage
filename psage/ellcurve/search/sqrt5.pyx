include 'stdsage.pxi'
include 'interrupt.pxi'
include 'cdefs.pxi'
include 'gmp.pxi'

from sage.rings.number_field.number_field_ideal import is_NumberFieldFractionalIdeal
from psage.number_fields.sqrt5 import F, a

from sage.rings.integer cimport Integer

cdef struct root5_element:
    # An element of the ring of integers of Q(sqrt 5)
    # This is stored as x + phi*y.
    long x
    long y

cdef struct a4a6_curve:
    # struct to store a curve over F = Q(sqrt 5)
    # in a quickly accessible manner.
    #
    # Since we are going to be working with short Weierstrass form
    # everywhere, we just store a4 and a6.
    #
    root5_element a4
    root5_element a6

def sieve_search(conductor, ap_dict):
    r"""
    search for a curve of the given conductor that has ap(e) = ap_dict[p] for
    all p in ap_dict. e.g. something like the following should work:

    examples:
        sage: from psage.number_fields.sqrt5.misc import f, a
        sage: sieve_search(5*a - 2, {2 : -3})
        elliptic curve...

    (except that isn't actually going to work for now because i am going to
    work with short weierstrass form).
    """

    # there are a few possibilities for how to proceed. we can either use
    # all of the primes that we are given immediately, and work modulo their
    # product, or we can try to get lucky by dealing with a smaller set of
    # primes to start with.

    # either way, the first thing that we need to do is: for each p make a
    # list of the curves mod p that have the correct a_p.

    # to make a list of all curves over o_k/(p), we need a list
    # of elements that are unique when we reduce them mod p
    
    # maybe there is a better way to do this, but for now we will
    # just constuct the residue field and lift all of its elements.

    cdef root5_element alpha
    cdef root5_element ** possible_coefficients
    cdef Integer x
    cdef Integer y
    possible_coefficients = <root5_element**>sage_malloc( len(ap_dict) * sizeof(root5_element*) )

    p_list = sorted(ap_dict.keys())

    for n, p in enumerate(p_list):
        if not is_NumberFieldFractionalIdeal(p):
            # assume that p is a fast sqrt5 ideal...
            p = p.sage_ideal()
        else:
            p = p
        k = p.residue_field()
        coefficients = [F(k.lift(x)) for x in k]
        
        # these should now all be of the type numberfieldelement_quadratic.
        # this has a method parts() which will return a and b so that
        # x = a + b sqrt(5). we want to work with the basis (1, phi),
        # so we convert this.

        possible_coefficients[n] = <root5_element*>sage_malloc( len(coefficients) )
        for m, z in enumerate(coefficients):
            c,d = z.parts()
            y = 2 * d
            x = c - d
            alpha.x = mpz_get_si(x.value)
            alpha.y = mpz_get_si(y.value)
            possible_coefficients[n][m] = alpha


def sieve_search_single_prime(conductor, p, ap):
    r"""
    search for a curve of the given conductor that has ap(E) = a, e.g.,
    the following should work

    examples:
        sage: from psage.number_fields.sqrt5.misc import f, a
        sage: sieve_search(5*a - 2, 2, -3)
        elliptic curve...

    (except that isn't actually going to work for now because i am going to
    work with short weierstrass form).
    """

    pass

    # there are a few possibilities for how to proceed. we can either use
    # all of the primes that we are given immediately, and work modulo their
    # product, or we can try to get lucky by dealing with a smaller set of
    # primes to start with.

    # either way, the first thing that we need to do is: for each p make a
    # list of the curves mod p that have the correct a_p.

    # to make a list of all curves over o_k/(p), we need a list
    # of elements that are unique when we reduce them mod p
    
    # maybe there is a better way to do this, but for now we will
    # just constuct the residue field and lift all of its elements.

#    cdef root5_element alpha
#    cdef root5_element ** possible_coefficients
#    cdef Integer x
#    cdef Integer y
#    possible_coefficients = <root5_element**>sage_malloc( len(ap_dict) * sizeof(root5_element*) )
#
#    
#
#    p_list = sorted(ap_dict.keys())
#
#    for n, p in enumerate(p_list):
#        if not is_numberfieldfractionalideal(p):
#            # assume that p is a fast sqrt5 ideal...
#            p = p.sage_ideal()
#        else:
#            p = p
#        k = p.residue_field()
#        coefficients = [f(k.lift(x)) for x in k]
#        
#        # these should now all be of the type numberfieldelement_quadratic.
#        # this has a method parts() which will return a and b so that
#        # x = a + b sqrt(5). we want to work with the basis (1, phi),
#        # so we convert this.
#
#        possible_coefficients[n] = <root5_element*>sage_malloc( len(coefficients) )
#        for m, z in enumerate(coefficients):
#            c,d = z.parts()
#            y = 2 * d
#            x = c - d
#            alpha.x = mpz_get_si(x.value)
#            alpha.y = mpz_get_si(y.value)
#            possible_coefficients[n][m] = alpha
