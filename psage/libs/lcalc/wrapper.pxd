cdef extern from "cmath":
    double sqrt(double)
    double log(double)
    double abs(double)
    double exp(double)

cdef extern from "<vector>" namespace "std":
    cdef cppclass vector[T]:
        cppclass iterator:
            T operator*()
            iterator operator++()
            bint operator==(iterator)
            bint operator!=(iterator)
        vector()
        void push_back(T&)
        T& operator[](int)
        T& at(int)
        iterator begin()
        iterator end()

cdef extern from "L.h":
    cdef void initialize_globals()
    ctypedef struct Complex "Complex":
        double real()
        double imag()
    cdef cppclass L_function[T]:
        double complex value(double complex s, int derivative, char * return_type) 
        L_function(char *NAME, int what_type, int N, T *coeff, long long Period, double q,  T w, int A, double *g, T *l, int n_poles, T *p, T *r)
        L_function()
        int find_zeros(long count, double * output_zeros, long start_N, double max_refine, int rank)
        void find_zeros_v(double t1, double t2, double step_size, vector[double]* result)
        #T (* value)
        #ctypedef struct c_Lfunction_C "L_function<Complex>":
        #c_Complex (* value) (c_Complex s, int derivative)
        #double (* N) (double T)
        #void  (* find_zeros_v)(double T1, double T2, double stepsize, doublevec result )
        #void (*find_zeros_via_N_v)(long count,int do_negative,double max_refine, int rank, int test_explicit_formula, doublevec result)
        #void (*print_data_L)()

        #Constructor and destructor
        #c_Lfunction_C *new_c_Lfunction_C "new L_function<Complex>"(char *NAME, int what_type, int N, c_Complex *coeff, long long Period, double q,  c_Complex w, int A, double *g, c_Complex *l, int n_poles, c_Complex *p, c_Complex *r)
        #cdef void del_c_Lfunction_C "delete"(c_Lfunction_C *L)


