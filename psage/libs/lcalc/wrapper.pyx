#
# TODO:
#   I am currently just trying to make this work as quickly as possible for
#   things that I want right now. But anyway...
#
#   - It is much too easy to make this segfault by giving bad input. Fix this.
#   - Use the precision information available in lcalc instead of pretending
#       that everything is computed to a full 53 bits
#   - Create classes DirichletLFunction, EllipticCurveLFunction, etc... (maybe with better names)
#   - Add constructors for creating L-functions from Gamma_R, Gamma_C

from cython.operator cimport dereference as deref, preincrement as inc #dereference and increment operators

include "interrupt.pxi"
include "cdefs.pxi"
include "stdsage.pxi"

from sage.modular.dirichlet import DirichletCharacter
from sage.schemes.elliptic_curves.ell_rational_field import EllipticCurve_rational_field
from sage.all import RR, CC, EllipticCurve

try:
    from dirichlet_conrey import DirichletCharacter_conrey
except:
    DirichletCharacter_conrey = type(None) # this is probably a bad way to do this

initialize_globals()

cdef double pi = 3.14159265358979

def number_of_coefficients_needed(Q, kappas, lambdas, max_t):
    # We completely mimic what lcalc does when it decides whether
    # to print a warning. 
    
    cdef int DIGITS = 14    # These are names of lcalc parameters, and we are
    cdef int DIGITS2 = 2    # mimicking them. Right now we are setting them
                            # to the default values set by initialize_globals() (I hope).
                            # We could try allowing them to be changed sometime in the
                            # future, especially if we are going to use multiprecision

    cdef double theta = sum(kappas)
    cdef double c = DIGITS2 * log(10.0)
    cdef int a = len(kappas)

    cdef double c1 = 0.0
    cdef double t0
    for j in range(a):
        t0 = kappas[j] * max_t + complex(lambdas[j]).imag
        if abs(t0) < 2 * c/ (pi * a):
            c1 += kappas[j] * pi/2.0
        else:
            c1 += kappas[j] * abs(c/(t0 * a))
    
    return Q * exp( log(2.3 * DIGITS * theta/c1) * theta) + 10

def Lfunction(X = None, max_t = 1000):
    """
    Create and return the L-function associated with X. If X is none, return the Riemann zeta function.

    EXAMPLES:

        sage: from psage.libs.lcalc.wrapper import Lfunction
        sage: L = Lfunction()
        sage: L(.5).real
        -1.4603545088096...
        sage: L.find_zeros(1)[0]
        14.134725141737...
        sage: G = DirichletGroup(11)
        sage: chi = G[5]
        sage: Lchi = Lfunction(chi)
        sage: Lchi.find_zeros(1)[0]
        2.4772437112...
    """

    if X is None:
        return Lfunction_class()
    
    if isinstance(X, (DirichletCharacter, DirichletCharacter_conrey)):
        return Lfunction_from_character(X)

    if isinstance(X, EllipticCurve_rational_field):
        return Lfunction_from_elliptic_curve(X, max_t)

    if isinstance(X, str):
        # for now we assume that X specifies an elliptic curve.
        # in the future other things will hopefully be supported
        try:
            E = EllipticCurve(X)
            return Lfunction_from_elliptic_curve(E, max_t)
        except KeyError:
            raise NotImplementedError("Right now only Cremona labels for elliptic curves are the only strings we can handle.")

    raise NotImplementedError("Not supported yet.")

    
def Lfunction_from_character(chi):
    if (not chi.is_primitive()):
        raise TypeError("Dirichlet character is not primitive")

    cdef int N = chi.modulus()
    cdef int a
    if chi.is_even():
        a = 0
    else:
        a = 1

    cdef double Q = sqrt(N/pi)
    cdef double complex gauss_sum = chi.gauss_sum()
    cdef double complex epsilon
    if a == 0:
        epsilon = gauss_sum/sqrt(N)
    else:
        epsilon = -1.0j * gauss_sum/sqrt(N)

    coefficients = [ complex(chi(n)) for n in xrange(0, N + 1) ]

    return Lfunction_class( name            = "L(s, chi)",
                            lcalc_type      = 1,
                            coefficients    = coefficients,
                            period          = N,
                            Q               = Q,
                            epsilon         = epsilon,
                            kappas          = [.5],
                            lambdas         = [a/2.0],
                            poles           = [],
                            residues        = [])

def Lfunction_from_elliptic_curve(E, max_t = 1000):

    cdef int N = E.conductor()
    Q = sqrt(N)/(2.0 * pi)
    kappas = [1.0]
    lambdas = [.5]

    cdef int number_of_coefficients = number_of_coefficients_needed(Q, kappas, lambdas, max_t)
    an_list = E.anlist(number_of_coefficients)
    #
    # normalize the coefficients to get analytic normalization
    #
    coefficients = [0] + [an_list[n]/sqrt(n) for n in xrange(1, number_of_coefficients)]

    return Lfunction_class( name            = "L(s, E)",    # this should be better.
                            lcalc_type      = 2,            # type specifies cusp form
                            coefficients    = coefficients,
                            period          = 0,            # NOT PERIODIC
                            Q               = Q,
                            epsilon         = E.root_number(),
                            kappas          = kappas,
                            lambdas         = lambdas,
                            poles           = [],           # There is a paper about this...
                            residues        = [])

cdef complex_list_to_array(double complex * output, input):
    for n in range(len(input)):
        output[n] = input[n]

cdef double_list_to_array(double * output, input):
    for n in range(len(input)):
        output[n] = input[n]

cdef class Lfunction_class:
    cdef readonly int lcalc_type, period
    cdef readonly char * name
    cdef _name
    cdef readonly double complex epsilon
    cdef readonly double Q
    cdef readonly int number_of_coefficients
    cdef readonly int number_of_kappas
    cdef readonly int number_of_poles
    cdef double complex *coefficients, *lambdas, *poles, *residues
    cdef double * kappas
    cdef L_function[double complex] * thisptr
    def __cinit__(self,
                 name = "Riemann zeta function",
                 lcalc_type = -1,
                 coefficients = [1,1,1,1,1],
                 period = 1,
                 Q = 0.564189583547756,
                 epsilon = 1,
                 kappas = [.5],
                 lambdas = [0],
                 poles = [0,1],
                 residues = [1,-1]):
        """
        Creates an L-function with functional equation of the type
        
            \Lambda(s) = \epsilon \overline{\Lambda(1- \bar s)}

        where the gamma factors look like
            
            Lambda(s) = Q^s \left( \prod_{j=1}^a \Gamma(\kappa_j s + \lambda_j) \right) L(s).

        NOTE: The nth coefficient passed should be the coefficient of a_n, so the 0th coefficient
        should be 0. (It will be ignored, anyway.)
        """

        # first we store all of the initialization data so that we have
        # access to it later.

        self._name      = name
        self.name       = self._name
        self.lcalc_type = lcalc_type
        self.period     = period
        self.Q          = Q
        self.epsilon    = epsilon

        self.number_of_coefficients     = len(coefficients)
        self.number_of_kappas           = len(kappas)
        self.number_of_poles            = len(poles)

        self.coefficients = <double complex*>malloc(    (self.number_of_coefficients) * sizeof(double complex))
        self.kappas       = <double *>       malloc(    (self.number_of_kappas + 1)   * sizeof(double))
        self.lambdas      = <double complex*>malloc(    (self.number_of_kappas + 1)   * sizeof(double complex))
        self.poles        = <double complex*>malloc(    (self.number_of_poles + 1)    * sizeof(double complex))
        self.residues     = <double complex*>malloc(    (self.number_of_poles + 1)    * sizeof(double complex))
        
        complex_list_to_array(self.coefficients, coefficients)
        double_list_to_array(self.kappas, [0] + kappas)
        complex_list_to_array(self.lambdas, [0] + lambdas)
        complex_list_to_array(self.poles, [0] + poles)
        complex_list_to_array(self.residues, [0] + residues)

        # If we are constucting the zeta function, we just call the default constructor...
        
        if self._name == "Riemann zeta function":
            self.thisptr = new L_function[double complex]()
        else:
            self.thisptr = new L_function[double complex](self.name, self.lcalc_type, self.number_of_coefficients - 1, self.coefficients, self.period, self.Q, self.epsilon, self.number_of_kappas, self.kappas, self.lambdas, self.number_of_poles, self.poles, self.residues)

    def __dealloc__(self):
        free(self.coefficients)
        free(self.kappas)
        free(self.lambdas)
        free(self.poles)
        free(self.residues)

    def value(self, double complex s, int derivative = 0):
        return self.thisptr.value(s, derivative, "pure")

    def Z(self, double complex x, int derivative = 0):
        cdef double complex s = .5 + x*1j
        return_value = self.thisptr.value(s, derivative, "rotated pure")
        if x.imag == 0:
            return return_value.real
        else:
            return return_value

    def find_zeros(self, int count, int start = 0, double max_refine = 1025):
        cdef double * zeros = <double*>malloc(count * sizeof(zeros))
        cdef int return_value = self.thisptr.find_zeros(count, zeros, start, max_refine, -2)
        zeros_list = []
        for n in range(count):
            zeros_list.append(zeros[n])
        free(zeros)
        return zeros_list

    def find_zeros_in_interval(self, double t1, double t2, double stepsize):
        cdef vector[double] *zeros = new vector[double]()
        #cdef vector[double] zeros
        self.thisptr.find_zeros_v(t1, t2, stepsize, zeros)
        zeros_list = []
        cdef vector[double].iterator it = zeros.begin()
        while it != zeros.end():
            zeros_list.append(deref(it))
            inc(it)

        del zeros
        return zeros_list

    def __call__(self, double complex s):
        return self.value(s)

