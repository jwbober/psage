include 'stdsage.pxi'
include 'interrupt.pxi'

from libc.stdint cimport int_fast8_t, int_fast16_t, int_fast32_t, \
                    int_fast64_t, uint_fast8_t, uint_fast16_t, \
                    uint_fast32_t, uint_fast64_t
from psage.ellcurve.minmodel.sqrt5 import canonical_model
from psage.libs.smalljac.wrapper1 import elliptic_curve_ap
from psage.number_fields.sqrt5 import F, a
from psage.number_fields.sqrt5.prime cimport Prime
from sage.schemes.elliptic_curves.constructor import EllipticCurve
from sage.rings.integer cimport Integer

cdef extern from 'pari/pari.h':
    uint_fast32_t Fl_sqrt(uint_fast32_t, uint_fast32_t)

cdef extern from 'math.h':
    double sqrt(double)
    double cbrt(double)

cdef struct condListNode:
    int_fast16_t cond[3], (*primeFactors)[4]
    uint_fast16_t condNorm
    uint_fast8_t numFactors

cdef struct F_curve:
    int_fast8_t a2[2]
    int_fast32_t a4[2], a6[2]
    int_fast64_t disc[2]
    uint_fast8_t a1[2], a3[2]

ctypedef uint_fast16_t GF_E[2]
ctypedef uint_fast16_t mod_n_E[4]

cdef uint_fast8_t pp_mod_256[256]
cdef uint_fast16_t i
for i in range(256ul):
    pp_mod_256[i] = 0u
pp_mod_256[  0] = 1u
pp_mod_256[  1] = 1u
pp_mod_256[ 17] = 1u
pp_mod_256[ 33] = 1u
pp_mod_256[ 49] = 1u
pp_mod_256[ 65] = 1u
pp_mod_256[ 81] = 1u
pp_mod_256[ 97] = 1u
pp_mod_256[113] = 1u
pp_mod_256[129] = 1u
pp_mod_256[145] = 1u
pp_mod_256[161] = 1u
pp_mod_256[177] = 1u
pp_mod_256[193] = 1u
pp_mod_256[209] = 1u
pp_mod_256[225] = 1u
pp_mod_256[241] = 1u

cdef inline uint_fast64_t sqrt_floor(uint_fast64_t n):
    cdef uint_fast64_t ret
    ret = <uint_fast64_t>sqrt(<double>n)
    while ret*ret < n: ret += 1ull
    while ret*ret > n: ret -= 1ull
    return ret

cdef inline uint_fast64_t cbrt_floor(uint_fast64_t n):
    cdef uint_fast64_t ret
    ret = <uint_fast64_t>cbrt(<double>n)
    while ret*ret*ret < n: ret += 1ull
    while ret*ret*ret > n: ret -= 1ull
    return ret

cdef inline uint_fast16_t integral_crt(uint_fast16_t s, uint_fast16_t t, \
        uint_fast16_t m_inv_mod_n, uint_fast16_t n):
    return ((n+t-s)*m_inv_mod_n+s)%n

cdef uint_fast16_t inv_mod_n(uint_fast16_t s, uint_fast16_t n):
    cdef uint_fast16_t t,u1,u2,v1,v2
    if s == 1ul: return s
    v1, v2 = 1ul, (n-n/s)%n
    u1, u2 = s, v2*s%n
    while u2 > 1ul:
        t = u1/u2
        v1, v2 = v2, (n+v1-t*v2%n)%n
        u1, u2 = u2, (n+u1-t*u2%n)%n
    return v2

cdef object ainvs(F_curve *curve):
    return curve.a1[0] + curve.a1[1]*a, curve.a2[0] + curve.a2[1]*a, \
            curve.a3[0] + curve.a3[1]*a, curve.a4[0] + curve.a4[1]*a, \
            curve.a6[0] + curve.a6[1]*a

cdef object ainvs_g(F_curve *curve):
    return curve.a1[0] + curve.a1[1]*(1-a), curve.a2[0] + curve.a2[1]*(1-a), \
            curve.a3[0] + curve.a3[1]*(1-a), curve.a4[0] + curve.a4[1]*(1-a), \
            curve.a6[0] + curve.a6[1]*(1-a)

cdef object E_tuple(F_curve *curve):
    return curve.a1[0], curve.a1[1], curve.a2[0], curve.a2[1], curve.a3[0], \
            curve.a3[1], curve.a4[0], curve.a4[1], curve.a6[0],  curve.a6[1]

cdef void fast_disc(F_curve *curve):
    cdef int_fast8_t b2[2], *a2
    cdef int_fast16_t b4[2], b6[2]
    cdef int_fast32_t b8[2], *a4, *a6
    cdef int_fast64_t *disc, t1, t2, t3
    cdef uint_fast8_t *a1, *a3

    a1 = curve.a1
    a2 = curve.a2
    a3 = curve.a3
    a4 = curve.a4
    a6 = curve.a6
    disc = curve.disc

    # b2 = a1^2 + 4*a2
    b2[0] = a1[0] + a1[1]
    b2[1] = a1[1]*(a1[0]+b2[0]) + (a2[1]<<2)
    b2[0] += a2[0]<<2

    # b8 = a1^2*a6 + 4*a2*a6
    b8[0] = b2[1]*a6[1]
    b8[1] = b2[0]*a6[1] + b2[1]*a6[0] + b8[0]
    b8[0] += b2[0]*a6[0]

    # b4 = a1*a3
    b4[0] = a1[1]&a3[1]
    b4[1] = b4[0] + (a1[0]&a3[1]) + (a1[1]&a3[0])
    b4[0] += a1[0]&a3[0]

    # b8 = a1^2*a6 + 4*a2*a6 - a1*a3*a4
    t1 = a4[1]*b4[1]
    b8[1] -= t1 + a4[0]*b4[1] + a4[1]*b4[0]
    b8[0] -= t1 + a4[0]*b4[0]

    # b4 = 2*a4 + a1*a3
    b4[0] += a4[0]<<1
    b4[1] += a4[1]<<1

    # b6 = a3^2
    b6[0] = a3[0] + a3[1]
    b6[1] = a3[1]*(a3[0]+b6[0])

    # b8 = a1^2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3^2
    t1 = a2[1]*b6[1]
    b8[1] += t1 + a2[0]*b6[1] + a2[1]*b6[0]
    b8[0] += t1 + a2[0]*b6[0]

    # b6 = a3^2 + 4*a6
    b6[0] += a6[0]<<2
    b6[1] += a6[1]<<2

    # b8 = a1^2*a6 + 4*a2*a6 - a1*a3*a4 + a2*a3^2 - a4^2
    t1 = a4[1]*a4[1]
    b8[0] -= t1 + a4[0]*a4[0]
    b8[1] -= t1 + ((a4[0]*a4[1])<<1)

    # disc = -3*b6 + b2*b4
    disc[0] = b2[1]*b4[1]
    disc[1] = disc[0] + b2[1]*b4[0] + b2[0]*b4[1] - 3*b6[1]
    disc[0] += b2[0]*b4[0] - 3*b6[0]

    # disc = -27*b6^2 + 9*b2*b4*b6
    t1 = b6[1]*disc[1]
    disc[1] = 9*(t1 + b6[1]*disc[0] + b6[0]*disc[1])
    disc[0] = 9*(t1 + disc[0]*b6[0])

    # disc = -8*b4^3 - 27*b6^2 + 9*b2*b4*b6
    t1 = b4[0]*b4[0]
    t2 = b4[1]*b4[1]
    t3 = (b4[1]+3*b4[0])*t2
    disc[1] -= t3 + (t2+3*t1)*b4[1]<<3
    disc[0] -= t3 + t1*b4[0]<<3

    # disc = -b2^2*b8 - 8*b4^3 - 27*b6^2 + 9*b2*b4*b6
    t1 = b2[0]*b2[0]+b2[1]*b2[1]
    t2 = ((b2[0]<<1)+b2[1])*b2[1]
    t3 = t2*b8[1]
    disc[1] -= t3 + b8[0]*t2 + b8[1]*t1
    disc[0] -= t3 + t1*b8[0]

cdef mod_n_E *split_prime_combine(GF_E *list0, GF_E *list1, \
        uint_fast32_t size0, uint_fast32_t size1, \
        uint_fast16_t p, uint_fast16_t r0, uint_fast16_t r1):
    cdef uint_fast16_t diff_inv
    cdef uint_fast32_t j, k
    cdef mod_n_E *ret, *liftptr
    cdef GF_E *start1
    cdef uint_fast16_t *E, *F, *lift
    diff_inv = inv_mod_n(r1-r0,p)
    ret = <mod_n_E *>sage_malloc(sizeof(mod_n_E)*size0*size1)
    liftptr = ret
    start1 = list1
    for j in range(size0):
        E = list0[0]
        list1 = start1
        for k in range(size1):
            F = list1[0]
            lift = liftptr[0] 
            lift[1] = (p+F[0]-E[0])*diff_inv%p
            lift[0] = (p+F[0]-lift[1]*r1%p)%p
            lift[3] = (p+F[1]-E[1])*diff_inv%p
            lift[2] = (p+F[1]-lift[3]*r1%p)%p
            if E[0] == 3 and E[1] == 8 and F[0] == 8 and F[1] == 8:
                print lift[0]+lift[1]*a,lift[2]+lift[3]*a
            liftptr += 1
            list1 += 1
        list0 += 1
    return ret

cdef class SievedSearch:

    cdef condListNode *__condList
    cdef F_curve __cur
    cdef GF_E ***__curves
    cdef int_fast32_t __r[2], __s[2], __t[2], __pst[2]
    cdef uint_fast8_t __numP
    cdef uint_fast16_t *__pList, *__rList, __N, __inv3, __invU4, __invU6
    cdef uint_fast16_t __numCond
    cdef uint_fast32_t **__sizes
    cdef object __ret

    def __cinit__(self, *args):
        cdef uint_fast8_t i
        cdef uint_fast16_t p, r0, r1
        for arg in args:
            if arg%5 not in (1,4) or not arg.is_prime():
                raise ValueError
        self.__numP = len(args)
        p_list = sorted(args)
        self.__pList = <uint_fast16_t *>sage_malloc( \
                sizeof(uint_fast16_t)*self.__numP)
        self.__rList = <uint_fast16_t *>sage_malloc( \
                sizeof(uint_fast16_t)*self.__numP*2)
        self.__N = 1ul
        for i in range(self.__numP):
            p = p_list[i]
            self.__pList[i] = p
            self.__N *= p
            r0 = Fl_sqrt(5ul, p)+1ul
            r1 = ((p+1ul)>>1ul)*r0%p
            r0 = p+1ul-r1
            if r0 > r1:
                r0, r1 = r1, r0
            self.__rList[2*i] = r0
            self.__rList[2*i+1] = r1
        self.__curves = <GF_E ***>sage_malloc( sizeof(GF_E **)*self.__numP)
        self.__sizes = <uint_fast32_t **>sage_malloc( \
                sizeof(uint_fast32_t *)*self.__numP)
        for i in range(self.__numP):
            self.__init_curves_in_GF(i)
        self.__pst[0] = 0ul
        self.__pst[1] = self.__N+1ul>>1ul
        if self.__N%3ul == 1ul: self.__inv3 = (2ul*self.__N+1ul)/3ul
        else: self.__inv3 = (self.__N+1ul)/3ul

    cdef void __init_curves_in_GF(self, uint_fast16_t i):
        cdef uint_fast16_t ap_shift, two_sqrtp, bad_shift
        cdef uint_fast16_t num_ap, j, k, p, cur_index
        cdef uint_fast32_t *cur_len
        p = self.__pList[i]
        two_sqrtp = sqrt_floor(p<<2ul)
        bad_shift = two_sqrtp+p+1ul
        num_ap = (two_sqrtp<<1ul)+1ul
        self.__curves[i] = <GF_E **>sage_malloc(sizeof(GF_E *)*num_ap)
        self.__sizes[i] = <uint_fast32_t *>sage_malloc( \
                sizeof(uint_fast32_t)*num_ap)
        cur_len = <uint_fast32_t *>sage_malloc(sizeof(uint_fast32_t)*num_ap)
        for j in range(num_ap):
            self.__sizes[i][j] = 0ul
        for k in range(p):
            for j in range(p):
                ap_shift = two_sqrtp + elliptic_curve_ap(k,j,p)
                if ap_shift != bad_shift:
                    if not self.__sizes[i][ap_shift]:
                        self.__curves[i][ap_shift] = <GF_E *>sage_malloc( \
                                sizeof(GF_E)<<4)
                        cur_len[ap_shift] = 16ul
                    cur_index = self.__sizes[i][ap_shift]
                    if cur_index == cur_len[ap_shift]:
                        cur_len[ap_shift] <<= 1ul
                        self.__curves[i][ap_shift] = <GF_E *>sage_realloc( \
                                self.__curves[i][ap_shift], \
                                sizeof(GF_E)*cur_len[ap_shift])
                    self.__curves[i][ap_shift][cur_index][0] = k
                    self.__curves[i][ap_shift][cur_index][1] = j
                    self.__sizes[i][ap_shift] += 1ul
        sage_free(cur_len)
        for j in range(num_ap):
            if self.__sizes[i][j]:
                self.__curves[i][j] = <GF_E *>sage_realloc( \
                        self.__curves[i][j], sizeof(GF_E)*self.__sizes[i][j])

    def __dealloc__(self):
        cdef uint_fast8_t i
        cdef uint_fast16_t j, num_ap
        for i in range(self.__numP):
            num_ap = (sqrt_floor(self.__pList[i]<<2ul)<<1ul)+1ul
            for j in range(num_ap):
                if self.__sizes[i][j]:
                    sage_free(self.__curves[i][j])
            sage_free(self.__curves[i])
            sage_free(self.__sizes[i])
        sage_free(self.__curves)
        sage_free(self.__sizes)
        sage_free(self.__pList)
        sage_free(self.__rList)

    cdef inline bint verify_cond(self, int_fast16_t *cond, uint_fast16_t i):
        E = EllipticCurve(F, list(ainvs(&self.__cur)))
        c = E.conductor()
        if c == cond[0]+cond[1]*a:
            c = cond[0]+cond[1]*a
            if c[0] < 0: c = -c
            self.__ret[c] = canonical_model(E.global_minimal_model())
            c = cond[0]+cond[1]*(1-a)
            if c[0] < 0: c = -c
            E = EllipticCurve(F, [b[0]+b[1]*(1-a) for b in E.ainvs()])
            self.__ret[c] = canonical_model(E)
            self.__numCond -= 1ul
            for j in range(i,self.__numCond):
                self.__condList[j] = self.__condList[j+1ul]
            return True
        return False

    cdef inline void run_curve(self):
        cdef uint_fast8_t j
        cdef int_fast16_t *p
        cdef uint_fast16_t i
        cdef int_fast64_t *disc, d[2], t[2]
        cdef uint_fast64_t t1, t2
        cdef double s
        cdef condListNode *cur
        cur = self.__condList
        fast_disc(&self.__cur)
        disc = self.__cur.disc
        if not disc[0] and not disc[1]: return
        for i in range(self.__numCond):
            d[0] = cur.cond[2]*disc[0]-cur.cond[1]*disc[1]
            if not d[0]%cur.condNorm:
                d[1] = cur.cond[0]*disc[1]-cur.cond[1]*disc[0]
                if not d[1]%cur.condNorm:
                    d[0] /= cur.condNorm
                    d[1] /= cur.condNorm
                    for j in range(cur.numFactors):
                        p = cur.primeFactors[j]
                        while True: 
                            t[0] = p[2]*d[0]-p[1]*d[1]
                            if t[0]%p[3]: break
                            t[1] = p[0]*d[1]-p[1]*d[0]
                            if t[1]%p[3]: break
                            d[0] = t[0]/p[3]
                            d[1] = t[1]/p[3]
                    if d[0] and d[1]:
                        s = (<double>d[0])/(<double>d[1])
                        s *= s+1
                        if s < 1:
                            t1 = d[1]*(d[1]-d[0])-d[0]*d[0]
                        elif s > 1:
                            t1 = d[0]*d[0]+d[1]*(d[0]-d[1])
                        else:
                            T = E_tuple(&self.__cur)
                            print("please check [%s+%s*a,%s+%s*a,%s"%T[:5] \
                                    +"+%s*a,%s+%s*a,%s+%s*a] by hand"%T[5:])
                            cur += 1
                            continue
                    elif d[0] < 0:
                        t1 = -d[0]
                    elif d[1] < 0:
                        t1 = -d[1]
                    else:
                        t1 = d[0]+d[1]
                    if pp_mod_256[t1&0xFFull]:
                        if t1%13ull < 2ull:
                            t2 = cbrt_floor(t1)
                            if t2*t2*t2 == t1:
                                t1 = sqrt_floor(t2)
                                if t1*t1 == t2:
                                    t2 = sqrt_floor(t1)
                                    if t2*t2 == t1:
                                        if self.verify_cond(cur.cond, i):
                                            return
            cur += 1

    cdef inline void set_a4a6(self, mod_n_E curve):
        cdef int_fast32_t t1, *r, *s, *t, *a4, *a6
        cdef uint_fast16_t N

        N = self.__N
        r = self.__r
        s = self.__s
        t = self.__t
        a4 = self.__cur.a4
        a6 = self.__cur.a6

        # a4' = a4 + 3*r^2; a6' = r^2
        a6[0] = r[1]*r[1]
        a6[1] = (a6[0] + (r[0]*r[1]<<1l))%N
        a6[0] = (a6[0] + r[0]*r[0])%N
        a4[0] = (3l*a6[0] + curve[0])%N
        a4[1] = (3l*a6[1] + curve[1])%N

        # a4' = a4 + 3*r^2 - 2*s*t
        t1 = s[1]*t[1]
        a4[0] = (a4[0] - (s[0]*t[0] + t1<<1l))%N
        a4[1] = (a4[1] - (s[0]*t[1] + s[1]*t[0] + t1<<1l))%N

        # a4' = u^-4*(a4 + 3*r^2 - 2*s*t)
        a4[0] = self.__invU4*a4[0]%N
        a4[1] = self.__invU4*a4[1]%N

        # a6' = a4 + r^2
        a6[0] = (a6[0] + curve[0])%N
        a6[1] = (a6[1] + curve[1])%N

        # a6' = a6 + r*a4 + r^3
        t1 = r[1]*a6[1]
        a6[1] = (r[0]*a6[1] + r[1]*a6[0] + t1 + curve[3])%N
        a6[0] = (r[0]*a6[0] + t1 + curve[2])%N

        # a6' = a6 + r*a4 + r^3 - t^2
        t1 = t[1]*t[1]
        a6[0] = (a6[0] - t[0]*t[0] - t1)%N
        a6[1] = (a6[1] - (t[0]*t[1]<<1l) - t1)%N

        # a6' = u^-6*(a6 + r*a4 + r^3 - t^2)
        a6[0] = self.__invU6*a6[0]%N
        a6[1] = self.__invU6*a6[1]%N

    cdef void lift_and_run(self, mod_n_E *curves, uint_fast64_t num_curves):
        cdef int_fast8_t a20, a21, *a2
        cdef int_fast32_t *r, *s, *t, *pst, *a4, *a6
        cdef uint_fast8_t a10, a11, *a1, a30, a31, *a3, u, u2, u3
        cdef uint_fast8_t j0, j1, j2, j3
        cdef uint_fast16_t N, N2, t1, t2
        cdef uint_fast64_t i
        cdef mod_n_E *lift

        N = self.__N
        N2 = N<<1u
        r = self.__r
        s = self.__s
        t = self.__t
        pst = self.__pst
        a1 = self.__cur.a1
        a2 = self.__cur.a2
        a3 = self.__cur.a3
        a4 = self.__cur.a4
        a6 = self.__cur.a6
        self.__ret = {}
        for u in (1,2,3,6):
            u2 = u*u%N
            u3 = u2*u%N
            self.__invU4 = inv_mod_n((<uint_fast16_t>u2)*u2%N, N)
            self.__invU6 = inv_mod_n((<uint_fast16_t>u2)*u3%N, N)
            for a10 in range(2):
                a1[0] = a10
                s[0] = pst[a10]*u%N
                t1 = s[0]*s[0]%N
                for a11 in range(2):
                    a1[1] = a11
                    s[1] = pst[a11]*u%N
                    t2 = s[1]*s[1]%N
                    t1 += t2
                    t2 += s[0]*s[1]<<1ul
                    for a20 in range(-1,2):
                        a2[0] = a20
                        r[0] = self.__inv3*(N+t1+a20*u2)%N
                        for a21 in range(-1,2):
                            a2[1] = a21
                            r[1] = self.__inv3*(N+t2+a21*u2)%N
                            for a30 in range(2):
                                a3[0] = a30
                                t[0] = pst[a30]*u3%N
                                for a31 in range(2):
                                    a3[1] = a31
                                    t[1] = pst[a31]*u3%N
                                    lift = curves
                                    for i in range(num_curves):
                                        self.set_a4a6(lift[0])
                                        for j0 in range(2):
                                            for j1 in range(2):
                                                for j2 in range(2):
                                                    for j3 in range(2):
                                                        self.run_curve()
                                                        if not self.__numCond:
                                                            return
                                                        a6[1] -= N
                                                    a6[1] += N2
                                                    a6[0] -= N
                                                a6[0] += N2
                                                a4[1] -= N
                                            a4[1] += N2
                                            a4[0] -= N
                                        lift += 1

    def __call__(self, conductors, ap):
        cdef condListNode *cur
        cdef mod_n_E **curves
        cdef int_fast16_t *pr
        cdef uint_fast16_t i, p, r0, r1, ap_shift0, ap_shift1
        cdef uint_fast64_t *lens
        cdef object cond

        if not isinstance(conductors, (list, tuple)):
            conductors = (conductors,)

        self.__numCond = len(conductors)
        self.__condList = <condListNode *> \
                sage_malloc(sizeof(condListNode)*self.__numCond)
        cur = self.__condList
        for i in range(self.__numCond):
            cond = F(conductors[i])
            cur.cond[0] = cond[0]
            cur.cond[1] = cond[1]
            cur.cond[2] = cur.cond[0]+cur.cond[1]
            cur.condNorm = cond.norm().abs()
            if cur.condNorm < 31:
                sage_free(self.__condList)
                raise ValueError("there are no conductors of norm < 31")
            f = cond.factor()
            cur.numFactors = len(f)
            cur.primeFactors = <int_fast16_t (*)[4]>sage_malloc( \
                    sizeof(int_fast16_t[4])*cur.numFactors)
            for j in range(cur.numFactors):
                pr = cur.primeFactors[j]
                pr[0] = f[j][0][0]
                pr[1] = f[j][0][1]
                pr[2] = pr[0]+pr[1]
                pr[3] = f[j][0].norm().abs()
            cur += 1
        lens = <uint_fast64_t *>sage_malloc(sizeof(uint_fast64_t)*self.__numP)
        curves = <mod_n_E **>sage_malloc(sizeof(mod_n_E *)*self.__numP)
        for i in range(self.__numP):
            p = self.__pList[i]
            r0, r1 = self.__rList[2*i], self.__rList[2*i+1]
            ap_shift0 = sqrt_floor(p<<2ul) + ap[Prime(p, r0, True)]
            ap_shift1 = sqrt_floor(p<<2ul) + ap[Prime(p, r1, False)]
            lens[i] = self.__sizes[i][ap_shift0]*self.__sizes[i][ap_shift1]
            curves[i] = split_prime_combine( \
                    self.__curves[i][ap_shift0], self.__curves[i][ap_shift1], \
                    self.__sizes[i][ap_shift0], self.__sizes[i][ap_shift1], \
                    p, r0, r1)

        #TODO: integral combine needs to go here

        self.lift_and_run(curves[0], lens[0])

        sage_free(lens)
        sage_free(curves)
        ret2 = tuple([self.__condList[i].cond[0] + \
                self.__condList[i].cond[1]*a for i in range(self.__numCond)])
        sage_free(self.__condList)
        return self.__ret, ret2
