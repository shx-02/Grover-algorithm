needs "Multivariate/transcendentals.ml";;

needs "Multivariate/cross.ml";;

needs "Multivariate/realanalysis.ml";;

needs "Library/grouptheory.ml";;

needs "Multivariate/cvectors.ml";;

needs "Multivariate/vectors.ml";;

needs "Library/binary.ml";;

needs "Library/words.ml";;

let IN_BITS_OF_NUM_LE = prove
(`!i x. 1 <= i /\ i <= dimindex (:(2,N)finite_pow) /\ x IN bits_of_num (i - 1) ==> x <= dimindex(:N) - 1`,
  SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN`i - 1 < 2 EXP dimindex (:N)`MP_TAC THENL[ASM_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ;SUBSET;IN_ELIM_THM] THEN
  ASM_SIMP_TAC[ARITH_RULE`1 <= a /\ i < a ==> i <= a - 1 `;DIMINDEX_GE_1] );;

let MAP_CONST = prove
 (`!l. MAP (\x:A. c:A) l = REPLICATE (LENGTH l) c`,
  LIST_INDUCT_TAC THENL[SIMP_TAC[MAP;REPLICATE;LENGTH];ALL_TAC]
  THEN ASM_SIMP_TAC[REPLICATE;LENGTH;MAP]);;

let REVERSE_REPLICATE = prove
(`!n:num c:A.
 REVERSE(REPLICATE n c) = REPLICATE n c`,
 INDUCT_TAC THENL[SIMP_TAC[REPLICATE;REVERSE];ALL_TAC] THEN
 SIMP_TAC[REPLICATE;REVERSE] THEN ASM_REWRITE_TAC[] THEN GEN_TAC THEN
 SPEC_TAC(`n:num`,`n:num`) THEN INDUCT_TAC THENL[SIMP_TAC[REPLICATE;
 APPEND];ALL_TAC] THEN ASM_SIMP_TAC[APPEND;REPLICATE]
 );;

let EL_REPLICATE = prove
(`!c:A x n:num .
 x < n ==> EL x (REPLICATE n c) = c`,
 GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL[ARITH_TAC;ALL_TAC] THEN
 STRIP_TAC THEN SUBGOAL_THEN`REPLICATE (SUC n) c = APPEND
 (REPLICATE n c) [c:A]`SUBST1_TAC THENL[GEN_REWRITE_TAC(LAND_CONV
 o ONCE_DEPTH_CONV)[GSYM REVERSE_REPLICATE] THEN SIMP_TAC[REPLICATE;REVERSE]
 THEN REWRITE_TAC[REVERSE_REPLICATE];ALL_TAC] THEN SIMP_TAC[EL_APPEND;
 LENGTH_REPLICATE] THEN ASM_CASES_TAC`x < n:num`
 THENL[ASM_SIMP_TAC[];ALL_TAC] THEN ASM_SIMP_TAC[] THEN MP_TAC(
 ARITH_RULE`~(x < n) /\ x < SUC n <=> x = n`) THEN
 ASM_SIMP_TAC[ARITH_RULE`n - n = 0`;EL;HD]
);;

let REVERSE_SING = prove
(`!n:A. REVERSE [n] = [n]`,
  MESON_TAC[REVERSE;APPEND;APPEND_SING]
);;

let LENGTH_SING = prove
(`!n:A. LENGTH [n] = 1`,
  SIMP_TAC[ARITH_RULE`1 = SUC 0`;LENGTH_EQ_CONS] THEN
  SIMP_TAC[LENGTH_EQ_NIL] THEN GEN_TAC THEN
  EXISTS_TAC`n:A` THEN EXISTS_TAC`[]:A list` THEN
  SIMP_TAC[]
);;

let REVERSE_LIST_OF_SEQ = prove
(`!n:num.0 < n ==> REVERSE(list_of_seq (\k. k) n) = list_of_seq (\k. n - 1 - k) n`,
  INDUCT_TAC THENL[ARITH_TAC;ALL_TAC] THEN SIMP_TAC[ ARITH_RULE`0 < SUC n`] THEN
  SIMP_TAC[list_of_seq;ARITH_RULE`SUC n - 1 = n`;SUB_REFL] THEN
  ASM_CASES_TAC`n <= 0` THENL[RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`n <= 0 <=> n = 0`]) THEN
  ASM_SIMP_TAC[list_of_seq;REVERSE;APPEND];ALL_TAC] THEN RULE_ASSUM_TAC(SIMP_RULE[
  ARITH_RULE`~(n <= 0) <=> 0 < n`]) THEN ASM_SIMP_TAC[REVERSE_APPEND;REVERSE_SING] THEN
  SIMP_TAC[APPEND_SING] THEN SIMP_TAC[LIST_EQ] THEN SIMP_TAC[LENGTH_APPEND;LENGTH_LIST_OF_SEQ] THEN
  SIMP_TAC[LENGTH_SING;EL_APPEND;EL_CONS] THEN ONCE_SIMP_TAC[GSYM APPEND_SING] THEN
  SIMP_TAC[LENGTH_APPEND;LENGTH_LIST_OF_SEQ;LENGTH_SING;ADD_SYM] THEN GEN_TAC THEN
  COND_CASES_TAC THENL[ASM_SIMP_TAC[EL_LIST_OF_SEQ;LENGTH_LIST_OF_SEQ;SUB];ALL_TAC] THEN
  COND_CASES_TAC THENL[ASM_SIMP_TAC[EL_LIST_OF_SEQ;LENGTH_LIST_OF_SEQ;
  ARITH_RULE`~(a = 0) ==> a < b + 1 ==> a - 1 < b`] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  COND_CASES_TAC THENL[ASM_SIMP_TAC[EL_LIST_OF_SEQ;LENGTH_LIST_OF_SEQ;ARITH_RULE`~(a = 0)
   ==> a < b + 1 ==> a - 1 < b`] THEN ASM_ARITH_TAC;ALL_TAC] THEN ASM_ARITH_TAC
);;

let UNION_DIFF = prove
(`!s t. s SUBSET t ==> t = s UNION (t DIFF s)`,
SIMP_TAC[SUBSET;EXTENSION;IN_ELIM_THM;UNION;DIFF] THEN
REPEAT STRIP_TAC THEN EQ_TAC THEN ASM_MESON_TAC[]);;

let BITSET_EQ_BITSNUM = prove
(`!a:num. bitset a = bits_of_num a `,
SIMP_TAC[bitset;bits_of_num;numbit]);;

let NUM_EXP_LE = prove
  (`!x y. 1 <= y ==> x <= x EXP y`,
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[EXP; ARITH] THEN
    SIMP_TAC[ARITH_RULE `1 <= SUC y <=> y = 0 \/ 1 <= y`] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[ARITH;EXP] THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `x * x:num` THEN
    ASM_SIMP_TAC[LE_SQUARE_REFL;LE_MULT_LCANCEL]);;

let is_qstate = new_definition
  `is_qstate (q:complex^M) <=> cnorm2 q = &1`;;

let finite_pow_tybij =
  let th = prove
   (`?x. x IN 1..(dimindex(:A) EXP dimindex(:B))`,
     EXISTS_TAC `1` THEN REWRITE_TAC[IN_NUMSEG; LE_REFL] THEN
     MESON_TAC[LE_1; DIMINDEX_GE_1; EXP_1;NUM_EXP_LE; LE_TRANS]) in
  new_type_definition "finite_pow" ("mk_finite_pow","dest_finite_pow") th;;

let FINITE_POW_IMAGE = prove
 (`UNIV:(A,B)finite_pow->bool =
       IMAGE mk_finite_pow (1..(dimindex(:A) EXP dimindex(:B)))`,
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_IMAGE] THEN
  MESON_TAC[finite_pow_tybij]);;

let DIMINDEX_HAS_SIZE_FINITE_POW = prove
 (`(UNIV:(M,N)finite_pow->bool) HAS_SIZE (dimindex(:M) EXP dimindex(:N))`,
  SIMP_TAC[FINITE_POW_IMAGE] THEN
  MATCH_MP_TAC HAS_SIZE_IMAGE_INJ THEN
  ONCE_REWRITE_TAC[DIMINDEX_UNIV] THEN REWRITE_TAC[HAS_SIZE_NUMSEG_1] THEN
  MESON_TAC[finite_pow_tybij]);;

let DIMINDEX_FINITE_POW = prove
    (`dimindex (:(M,N)finite_pow) = dimindex (:M) EXP dimindex (:N)`,
    GEN_REWRITE_TAC LAND_CONV [dimindex] THEN
  REWRITE_TAC[REWRITE_RULE[HAS_SIZE] DIMINDEX_HAS_SIZE_FINITE_POW]);;

let FINITE_INDEX_INRANGE2 = prove
 (`!i. ?k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
           (!x:A^(2,N)finite_pow. x$i = x$k) /\ (!y:B^(2,N)finite_pow. y$i = y$k)`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]);;

let cbasis = new_definition
  `cbasis k = vector_to_cvector(basis k :real^N) `;;

let CBASIS_COMPONENT = prove
 (`!k i. 1 <= k /\ k <= dimindex (:(2,N)finite_pow)
         ==> ((cbasis i :complex^(2,N)finite_pow)$k = if k = i then Cx(&1) else Cx(&0))`,
  SIMP_TAC[cbasis; LAMBDA_BETA;vector_to_cvector;vector_map;basis;COND_RAND] THEN MESON_TAC[]);;

let qstate_tybij =
  let th = prove
   (`?q:complex^(2,N)finite_pow. is_qstate q`,
     EXISTS_TAC `cbasis 1:complex^(2,N)finite_pow` THEN
    SIMP_TAC[is_qstate;CNORM2_ALT;cbasis;cdot] THEN
    SIMP_TAC[VECTOR_TO_CVECTOR_COMPONENT;BASIS_COMPONENT] THEN
    REWRITE_TAC[COND_RAND;CNJ_CX] THEN
    REWRITE_TAC[COND_RATOR;COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]
    THEN REWRITE_TAC[COMPLEX_MUL_LID; COMPLEX_MUL_RID]
    THEN SIMP_TAC[VSUM_DELTA] THEN
    REWRITE_TAC[GSYM COMPLEX_VEC_0;VSUM_DELTA] THEN
    SIMP_TAC[IN_NUMSEG;LE_REFL;DIMINDEX_GE_1] THEN
    SIMP_TAC[COMPLEX_NORM_CX] THEN REAL_ARITH_TAC) in
  new_type_definition "qstate" ("mk_qstate","dest_qstate") th;;

let QSTATE_NORM = prove
(`!q:(N)qstate.
    cnorm2(dest_qstate q) = &1`,
MESON_TAC[is_qstate;qstate_tybij]);;

let DEST_QSTATE_EQ = prove
 (`!x y. dest_qstate x = dest_qstate y <=> x = y`,
  MESON_TAC[qstate_tybij]);;

let DEST_OF_QSTATE = prove
 (`!q:complex^(2,N)finite_pow. is_qstate q
         ==> dest_qstate(mk_qstate q) = q`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [GSYM qstate_tybij] THEN
  ASM_REWRITE_TAC[]);;

(*Qstate operation*)
overload_interface ("--",`(qstate_neg):(N)qstate->(N)qstate`);;

overload_interface ("+",`(qstate_add):(N)qstate->(N)qstate->(N)qstate`);;

parse_as_infix("qdot",(20,"right"));;

let qstate_neg = new_definition
  `!q:(N)qstate. --q =
    mk_qstate (lambda i. --(dest_qstate q$i))`;;

let qstate_add = new_definition
  `qstate_add (q1:(N)qstate) (q2:(N)qstate) :(N)qstate =
    mk_qstate (lambda i. (dest_qstate q1$i + dest_qstate q2$i))`;;

parse_as_infix("%%%", (22, "right"));;

let qstate_cmul = new_definition
  `!c:complex q:(N)qstate. c %%% q = lambda i. c * (dest_qstate q)$i`;;

let qstate_cnj = new_definition
  `(qstate_cnj :(N)qstate -> (N)qstate) q =
    mk_qstate (lambda i. cnj (dest_qstate q$i))`;;

let qdot = new_definition
`(x:(N)qstate) qdot (y:(N)qstate) = vsum (1..dimindex(:(2,N)finite_pow)) (\i. dest_qstate x$i * cnj(dest_qstate y$i))`;;

let QDOT_SYM = prove
(`!x:(N)qstate y. x qdot y = cnj (y qdot x)`,
  REWRITE_TAC[qdot]
  THEN REWRITE_TAC[MATCH_MP (SPEC_ALL CNJ_VSUM) (SPEC `dimindex (:N)` (GEN_ALL
    (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[CNJ_MUL;CNJ_CNJ;COMPLEX_MUL_SYM]);;

(*tensor product*)
let tensor_pro_vec = new_definition
  `tensor_pro_vec (x:(N)qstate) (y:(M)qstate):((N,M)finite_sum)qstate =
   mk_qstate (lambda k. (dest_qstate x$((k - 1) DIV dimindex(:M) + 1)) *
                        (dest_qstate y$((k - 1) MOD dimindex(:M) + 1)))`;;

let tensor_pro_mat = new_definition
  `tensor_pro_mat (x:complex^(2,M)finite_pow^(2,N)finite_pow)
  (y:complex^(2,P)finite_pow^(2,Q)finite_pow):
  complex^((2,M)finite_pow,(2,P)finite_pow)finite_prod^((2,N)finite_pow,(2,Q)finite_pow)finite_prod =
  lambda i j. x$((i-1) DIV dimindex(:(2,P)finite_pow) + 1)$((j-1) DIV dimindex(:(2,Q)finite_pow) + 1) *
  y$((i-1) MOD dimindex(:(2,P)finite_pow) + 1)$((j-1) MOD dimindex(:(2,Q)finite_pow) + 1)`;;

(*complex matrix operation*)
overload_interface ("--",`(cmatrix_neg):complex^(2,N)finite_pow^(2,M)finite_pow ->complex^(2,N)finite_pow^(2,M)finite_pow`);;

overload_interface ("+",`(cmatrix_add):complex^(2,N)finite_pow^(2,M)finite_pow ->complex^(2,N)finite_pow^(2,M)finite_pow ->complex^(2,N)finite_pow^(2,M)finite_pow`);;

overload_interface ("-",`(cmatrix_sub):complex^(2,N)finite_pow^(2,M)finite_pow ->complex^(2,N)finite_pow^(2,M)finite_pow ->complex^(2,N)finite_pow^(2,M)finite_pow`);;

overload_interface ("**",`(cmatrix_qstate_mul):complex^((2,N)finite_pow)^((2,M)finite_pow)->(N)qstate->(M)qstate`);;

overload_interface ("**",`(cmatrix_mul):complex^(2,N)finite_pow^(2,M)finite_pow->complex^(2,P)finite_pow^(2,N)finite_pow->complex^(2,P)finite_pow^(2,M)finite_pow`);;

make_overloadable "%*" `:A->B->C`;;

overload_interface ("%*",`(cmatrix_cmul):complex-> complex^(2,N)finite_pow^(2,M)finite_pow -> complex^(2,N)finite_pow^(2,M)finite_pow`);;

parse_as_infix("%*",(21,"right"));;

let cmatrix_neg = new_definition
    `!A:complex^(2,N)finite_pow^(2,M)finite_pow. --A = lambda i j. --(A$i$j)`;;

let cmatrix_add = new_definition
    `!A B:complex^(2,N)finite_pow^(2,M)finite_pow. A + B = lambda i j. A$i$j + B$i$j`;;

let cmatrix_sub = new_definition
    `!A B:complex^(2,N)finite_pow^(2,M)finite_pow. A - B = lambda i j. A$i$j - B$i$j`;;

let cmatrix_cmul = new_definition
  `!c:complex A:complex^(2,N)finite_pow^(2,M)finite_pow. c %* A = lambda i j. c * A$i$j`;;

let cmatrix_qstate_mul = new_definition
  `!q:(N)qstate A:complex^((2,N)finite_pow)^((2,M)finite_pow). A ** q  =
   mk_qstate (lambda i. vsum (1..dimindex (:(2,N)finite_pow)) (\j. A$i$j * dest_qstate q$j))`;;

let ctransp = new_definition
  `(ctransp:complex^(2,N)finite_pow^(2,M)finite_pow->complex^(2,M)finite_pow^(2,N)finite_pow) A
        = lambda i j. A$j$i`;;

let cmatrix_cnj = new_definition
    `(cmatrix_cnj:complex^(2,N)finite_pow^(2,M)finite_pow->complex^(2,N)finite_pow^(2,M)finite_pow) A = lambda i j. cnj(A$i$j)`;;

let cmatrix_mul = new_definition
    `!A:complex^(2,N)finite_pow^(2,M)finite_pow B:complex^(2,P)finite_pow^(2,N)finite_pow. A ** B =
    lambda i j. vsum(1..dimindex(:(2,N)finite_pow)) (\k. A$i$k * B$k$j)`;;

let id_cmatrix = new_definition
`id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow =
                lambda i j.if i = j then Cx(&1) else Cx(&0)`;;

let hermitian_matrix = new_definition
    `(hermitian_matrix:complex^(2,N)finite_pow^(2,M)finite_pow->complex^(2,M)finite_pow^(2,N)finite_pow) A
      = lambda i j. cnj(A$j$i)`;;

let diagonal_cmatrix = new_definition
 `diagonal_cmatrix(A:complex^(2,N)finite_pow^(2,N)finite_pow) <=>
        !i j. 1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
              1 <= j /\ j <= dimindex(:(2,N)finite_pow) /\
              ~(i = j) ==> A$i$j = Cx(&0)`;;

let COND_RIGHT_F =
 prove
  (`(if b then b else F) = b`,
   BOOL_CASES_TAC `b:bool` THEN
   REWRITE_TAC []);;

let COND_T_F =
 prove
  (`(if b then  T else F) = b`,
   BOOL_CASES_TAC `b:bool` THEN
   REWRITE_TAC []);;

let COND_LMUL = prove
 (`!b x1 x2 y. (if b then x1 else x2) * y = (if b then x1 * y else x2 * y)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let COND_RMUL = prove
 (`!b x1 x2 y. y * (if b then x1 else x2) = (if b then y * x1 else y * x2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[]);;

let COND_LMUL_0 = prove
 (`!b x y. (if b then x else &0) * y = (if b then x * y else &0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[REAL_MUL_LZERO]);;

let COND_RMUL_0 = prove
 (`!b x y. y * (if b then x else &0) = (if b then y * x else &0)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[REAL_MUL_RZERO]);;

let COND_CNJ = prove
 (`!b x1 x2:complex. cnj(if b then x1 else x2) = (if b then cnj x1 else cnj x2)`,
  REPEAT GEN_TAC THEN BOOL_CASES_TAC `b:bool` THEN REWRITE_TAC[] THEN REWRITE_TAC[]);;

let VSUM_RESTRICT_ZERO = prove
 (`!P s f. vsum {x | x IN s /\ P x} f =
           vsum s (\x. if P x then f x else Cx(&0))`,
  SIMP_TAC[vsum; CART_EQ; LAMBDA_BETA; VEC_COMPONENT; SUM_RESTRICT_SET;
           COND_COMPONENT] THEN
           SIMP_TAC[DIMINDEX_2;FORALL_2;CX_DEF;complex;VECTOR_2]);;

let VSUM_DELTA_ALT = prove
 (`!s a. vsum s (\x. if x = a then b else Cx(&0)) =
         if a IN s then b else Cx(&0)`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VSUM_COMPONENT; COND_COMPONENT] THEN
  SIMP_TAC[DIMINDEX_2;FORALL_2;CX_DEF;complex;VECTOR_2;SUM_DELTA]);;

let IDCMAT = prove
 (`!i j.
        1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
        1 <= j /\ j <= dimindex(:(2,N)finite_pow)
        ==> (id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow)$i$j =
        if i = j then Cx(&1) else Cx(&0)`,
  REPEAT GEN_TAC THEN CHOOSE_TAC (SPEC_ALL FINITE_INDEX_INRANGE)
  THEN ASM_SIMP_TAC[id_cmatrix;LAMBDA_BETA]);;

let IDCMAT_HERMITIAN = prove
(`id_cmatrix = hermitian_matrix (id_cmatrix :complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[hermitian_matrix;cmatrix_cnj;id_cmatrix] THEN
SIMP_TAC[CART_EQ;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN MESON_TAC[]);;

let IDCMAT_DIAGONAL = prove
(`diagonal_cmatrix (id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[diagonal_cmatrix;id_cmatrix;LAMBDA_BETA] THEN MESON_TAC[]);;

let DIAGONAL_CMATRIX = prove
 (`!A:complex^(2,N)finite_pow^(2,N)finite_pow.
     diagonal_cmatrix A <=> A = (lambda i j. if i = j then A$i$j else Cx(&0))`,
  SIMP_TAC[CART_EQ; LAMBDA_BETA; diagonal_cmatrix] THEN MESON_TAC[]);;

let CMATRIX_SUB_COMPONENT = prove
 (`!A B:complex^(2,N)finite_pow^(2,M)finite_pow i j. (A - B)$i$j = A$i$j - B$i$j`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:(2,M)finite_pow) /\ !A:complex^(2,N)finite_pow^(2,M)finite_pow. A$i = A$k`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:(2,N)finite_pow) /\ !z:complex^(2,N)finite_pow. z$j = z$l`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE]; ALL_TAC] THEN
  ASM_SIMP_TAC[cmatrix_sub; LAMBDA_BETA]);;

let CTRANSP_COMPONENT = prove
 (`!A:complex^(2,N)finite_pow^(2,M)finite_pow i j. (ctransp A)$i$j = A$j$i`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
                    (!A:complex^(2,M)finite_pow^(2,N)finite_pow. A$i = A$k) /\ (!z:complex^(2,N)finite_pow. z$i = z$k)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE2]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:(2,M)finite_pow) /\
                    (!A:complex^(2,N)finite_pow^(2,M)finite_pow. A$j = A$l) /\ (!z:complex^(2,M)finite_pow. z$j = z$l)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE2]; ALL_TAC] THEN
  ASM_SIMP_TAC[ctransp; LAMBDA_BETA]);;

let CTRANSP_SUB = prove
(`!A:complex^(2,N)finite_pow^(2,M)finite_pow. ctransp (A-B) = ctransp A -ctransp B`,
GEN_TAC THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;ctransp;cmatrix_sub]);;

let CTRANSP_MUL = prove
(`!A B:complex^(2,N)finite_pow^(2,M)finite_pow. ctransp(A ** B) = (ctransp B) ** (ctransp A)`,
SIMP_TAC[ctransp;CART_EQ;LAMBDA_BETA;cmatrix_mul;COMPLEX_MUL_SYM]
);;

let CTRANSP_CMUL = prove
(`!A:complex^(2,N)finite_pow^(2,M)finite_pow c:complex. ctransp (c %* A) = c %* ctransp A`,
GEN_TAC THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;ctransp;cmatrix_cmul]);;

let CMATRIX_CNJ_SUB = prove
(`!A:complex^(2,N)finite_pow^(2,M)finite_pow. cmatrix_cnj (A-B) = cmatrix_cnj A - cmatrix_cnj B`,
GEN_TAC THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;cmatrix_cnj;cmatrix_sub;CNJ_SUB]);;

let CMATRIX_CNJ_MUL = prove
(`!A B:complex^(2,N)finite_pow^(2,M)finite_pow. cmatrix_cnj (A ** B) = cmatrix_cnj A ** cmatrix_cnj B`,
GEN_TAC THEN SIMP_TAC[cmatrix_mul;CART_EQ;LAMBDA_BETA;cmatrix_cnj;CNJ_VSUM;FINITE_NUMSEG;CNJ_MUL]
);;

let CMATRIX_CNJ_CMUL = prove
(`!A:complex^(2,N)finite_pow^(2,M)finite_pow c:complex. cmatrix_cnj (c %* A) = cnj c %* cmatrix_cnj A`,
GEN_TAC THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;cmatrix_cnj;cmatrix_cmul;CNJ_MUL]);;

let CMATRIX_ADD_LDISTRIB = prove
 (`!A:complex^(2,N)finite_pow^(2,M)finite_pow B:complex^(2,P)finite_pow^(2,N)finite_pow C.
  A ** (B + C) = A ** B + A ** C`,
  SIMP_TAC[cmatrix_mul; cmatrix_add; CART_EQ; LAMBDA_BETA;GSYM VSUM_ADD_NUMSEG] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  ASM_SIMP_TAC[LAMBDA_BETA;COMPLEX_ADD_LDISTRIB]);;

let CMATRIX_SUB_LDISTRIB = prove
 (`!A:complex^(2,N)finite_pow^(2,M)finite_pow B:complex^(2,P)finite_pow^(2,N)finite_pow C. A ** (B - C) = A ** B - A ** C`,
  SIMP_TAC[cmatrix_mul; cmatrix_sub; CART_EQ; LAMBDA_BETA;GSYM VSUM_SUB_NUMSEG] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  ASM_SIMP_TAC[LAMBDA_BETA;COMPLEX_SUB_LDISTRIB]);;

let CMATRIX_ADD_RDISTRIB = prove
 (`!B:complex^(2,N)finite_pow^(2,M)finite_pow C A:complex^(2,P)finite_pow^(2,N)finite_pow. (B + C) ** A = B ** A + C ** A`,
  SIMP_TAC[cmatrix_mul; cmatrix_add; CART_EQ; LAMBDA_BETA;GSYM VSUM_ADD_NUMSEG] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  ASM_SIMP_TAC[LAMBDA_BETA;COMPLEX_ADD_RDISTRIB]);;

let CMATRIX_SUB_RDISTRIB = prove
 (`!B:complex^(2,N)finite_pow^(2,M)finite_pow C A:complex^(2,P)finite_pow^(2,N)finite_pow. (B - C) ** A = B ** A - C ** A`,
  SIMP_TAC[cmatrix_mul; cmatrix_sub; CART_EQ; LAMBDA_BETA;GSYM VSUM_SUB_NUMSEG] THEN
  REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC VSUM_EQ_NUMSEG THEN
  ASM_SIMP_TAC[LAMBDA_BETA; COMPLEX_SUB_RDISTRIB]);;

let CMATRIX_MUL_ASSOC = prove
 (`!A:complex^(2,N)finite_pow^(2,M)finite_pow B:complex^(2,P)finite_pow^(2,N)finite_pow C:complex^(2,Q)finite_pow^(2,P)finite_pow.
 A ** B ** C = (A ** B) ** C`,
  REPEAT GEN_TAC THEN
  SIMP_TAC[cmatrix_mul; CART_EQ; LAMBDA_BETA; FINITE_NUMSEG;GSYM VSUM_COMPLEX_LMUL; GSYM VSUM_COMPLEX_RMUL] THEN
  REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
 GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV ) [VSUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let CTRANSP_DIAGONAL_CMATRIX = prove
 (`!A:complex^(2,N)finite_pow^(2,N)finite_pow. diagonal_cmatrix A ==> ctransp A = A`,
  GEN_TAC THEN REWRITE_TAC[diagonal_cmatrix; CART_EQ; CTRANSP_COMPONENT] THEN
  STRIP_TAC THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN X_GEN_TAC `j:num` THEN
  STRIP_TAC THEN ASM_CASES_TAC `i:num = j` THEN ASM_SIMP_TAC[]);;

let CMATRIX_MUL_DIAGONAL = prove
 (`!A B:complex^(2,N)finite_pow^(2,N)finite_pow.
        diagonal_cmatrix A /\ diagonal_cmatrix B
        ==> A ** B = lambda i j. A$i$j * B$i$j`,
  REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST1_TAC o GEN_REWRITE_RULE I [DIAGONAL_CMATRIX])) THEN
  SIMP_TAC[CART_EQ; cmatrix_mul; LAMBDA_BETA] THEN
  ONCE_REWRITE_TAC[MESON[COMPLEX_MUL_LZERO; COMPLEX_MUL_RZERO]
   `(if p then a else Cx(&0)) * (if q then b else Cx(&0)) =
    if q then (if p then a * b else Cx(&0)) else Cx(&0)`] THEN
  SIMP_TAC[VSUM_DELTA_ALT; IN_NUMSEG; COND_ID;]);;

let HERMITIAN = prove
(`!A:complex^(2,N)finite_pow^(2,M)finite_pow. hermitian_matrix A = cmatrix_cnj (ctransp A)`,
SIMP_TAC[hermitian_matrix;cmatrix_cnj] THEN
SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
                    (!A:complex^(2,M)finite_pow^(2,N)finite_pow. A$i = A$k) /\ (!z:complex^(2,N)finite_pow. z$i = z$k)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE2]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:(2,M)finite_pow) /\
                    (!A:complex^(2,N)finite_pow^(2,M)finite_pow. A$j = A$l) /\ (!z:complex^(2,M)finite_pow. z$j = z$l)`
  CHOOSE_TAC THENL [REWRITE_TAC[FINITE_INDEX_INRANGE2]; ALL_TAC] THEN
  ASM_SIMP_TAC[ctransp;CART_EQ;LAMBDA_BETA]);;

let HERMITIAN_MUL = prove
(`!A B:complex^(2,N)finite_pow^(2,M)finite_pow.
hermitian_matrix(A ** B) = (hermitian_matrix B) ** (hermitian_matrix A)`,
SIMP_TAC[HERMITIAN;CTRANSP_MUL;CMATRIX_CNJ_MUL]
);;

let HERMITIAN_SUB = prove
(`!A B:complex^(2,N)finite_pow^(2,M)finite_pow.
 hermitian_matrix(A - B) = hermitian_matrix A -hermitian_matrix B `,
REPEAT GEN_TAC THEN SIMP_TAC[HERMITIAN;CMATRIX_CNJ_SUB;CTRANSP_SUB]);;

let HERMITIAN_CMUL = prove
(`!A:complex^(2,N)finite_pow^(2,M)finite_pow c:complex. hermitian_matrix(c%*A) = cnj c %* hermitian_matrix A`,
REPEAT GEN_TAC THEN SIMP_TAC[HERMITIAN;CTRANSP_CMUL;CTRANSP_SUB;CMATRIX_CNJ_SUB;CMATRIX_CNJ_CMUL]);;

(*unitary matrix *)
let unitary_matrix = new_definition
  `unitary_matrix (U:complex^(2,N)finite_pow^(2,N)finite_pow) <=>
     hermitian_matrix U ** U = id_cmatrix /\ U ** hermitian_matrix U = id_cmatrix`;;

let UNITARY_ORTHOGONAL_THM = prove
(`!A:complex^(2,N)finite_pow^(2,N)finite_pow.
unitary_matrix A ==> (!x y. 1 <= x /\ x <= dimindex(:(2,N)finite_pow)
/\ 1 <= y /\ y <= dimindex(:(2,N)finite_pow)
==> vsum(1..dimindex(:(2,N)finite_pow)) (\i. A$i$x * cnj (A$i$y)) =
if x = y then Cx(&1) else Cx(&0))`,
SIMP_TAC[CART_EQ;LAMBDA_BETA;unitary_matrix;hermitian_matrix;cmatrix_mul;LAMBDA_BETA;id_cmatrix]
THEN SIMP_TAC[COND_COMPONENT;CX_DEF;complex;DIMINDEX_2;FORALL_2;VECTOR_2]
THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`A$i$x * cnj (A$i$y) = cnj (A$i$y) * A$i$x`]
THEN ARITH_TAC);;

let UNITARITY = prove
(`!A:complex^(2,N)finite_pow^(2,N)finite_pow q:(N)qstate.
     unitary_matrix A ==>
     cnorm2((lambda i. vsum (1..dimindex (:(2,N)finite_pow))
                (\j. A$i$j * dest_qstate q$j)):complex^(2,N)finite_pow) = &1`,
REPEAT GEN_TAC THEN SIMP_TAC[cnorm2;REAL_CDOT_SELF;REAL_OF_COMPLEX_RE;cdot; LAMBDA_BETA] THEN
SIMP_TAC[FINITE_NUMSEG;CNJ_VSUM;CNJ_MUL] THEN SIMP_TAC[BILINEAR_COMPLEX_MUL;FINITE_NUMSEG;BILINEAR_VSUM] THEN
SIMP_TAC[SIMPLE_COMPLEX_ARITH`(a * b) * c * d = a * c * b * d:complex`] THEN SIMP_TAC[FORALL_UNPAIR_THM] THEN
SUBGOAL_THEN`FINITE(1..dimindex (:(2,N)finite_pow)) /\ FINITE
  ((1..dimindex (:(2,N)finite_pow)) CROSS
           (1..dimindex (:(2,N)finite_pow)))  `ASSUME_TAC THENL
[SIMP_TAC[FINITE_NUMSEG;FINITE_CROSS];ALL_TAC] THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL  VSUM_SWAP)) THEN ASM_SIMP_TAC[]
THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`a * b * c * d = (c * d) * a * b:complex`]
THEN SIMP_TAC[FINITE_NUMSEG;VSUM_COMPLEX_LMUL] THEN SIMP_TAC[LAMBDA_PAIR_THM] THEN
POP_ASSUM (K ALL_TAC) THEN STRIP_TAC THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP UNITARY_ORTHOGONAL_THM) THEN
RULE_ASSUM_TAC(SIMP_RULE[TAUT`a /\ b /\ c /\ d <=> (a /\ b) /\ c /\ d`]) THEN SIMP_TAC[IN_NUMSEG;CROSS] THEN
SUBGOAL_THEN `(Re(vsum
  {x,y | (1 <= x /\ x <= dimindex (:(2,N)finite_pow)) /\
         1 <= y /\ y <= dimindex (:(2,N)finite_pow)}
 (\(x,y). (dest_qstate (q:(N)qstate)$x * cnj (dest_qstate q$y)) *
          vsum (1..dimindex (:(2,N)finite_pow)) (\i. (A:complex^(2,N)finite_pow^(2,N)finite_pow)$i$x * cnj (A$i$y)))) = &1)  =
 (Re(vsum {x,y | (1 <= x /\ x <= dimindex (:(2,N)finite_pow)) /\
         1 <= y /\ y <= dimindex (:(2,N)finite_pow)}
 (\(x,y). (dest_qstate q$x * cnj (dest_qstate q$y)) *
        (if x = y then Cx (&1) else Cx (&0)))) = &1)` SUBST1_TAC THENL
[AP_THM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM IN_NUMSEG]) THEN
SIMP_TAC[GSYM IN_NUMSEG;GSYM CROSS] THEN MATCH_MP_TAC VSUM_EQ
THEN ASM_SIMP_TAC[FORALL_IN_CROSS];ALL_TAC] THEN POP_ASSUM (K ALL_TAC) THEN ONCE_REWRITE_TAC[COND_RAND;COND_RATOR] THEN
SIMP_TAC[COMPLEX_MUL_RID;COMPLEX_MUL_RZERO] THEN ASSUME_TAC (SPEC_ALL QSTATE_NORM) THEN
RULE_ASSUM_TAC(SIMP_RULE[cnorm2;REAL_CDOT_SELF;REAL_OF_COMPLEX_RE;cdot]) THEN
SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;GSYM VSUM_VSUM_PRODUCT] THEN SIMP_TAC[GSYM VSUM_RESTRICT_ZERO]
THEN SIMP_TAC[SET_RULE`x IN 1.. dimindex(:(2,N)finite_pow) ==>
    {y | y IN 1..dimindex (:(2,N)finite_pow) /\ x = y} = {x}`] THEN ASM_SIMP_TAC[VSUM_SING]);;

let UNITARY_MUL = prove
(`!A B:complex^(2,N)finite_pow^(2,N)finite_pow.
  unitary_matrix A /\ unitary_matrix B ==> unitary_matrix (A ** B)`,
  REPEAT GEN_TAC THEN SIMP_TAC[unitary_matrix;HERMITIAN_MUL] THEN STRIP_TAC THEN
SIMP_TAC[GSYM CMATRIX_MUL_ASSOC] THEN SUBGOAL_THEN`(hermitian_matrix B:complex^(2,N)finite_pow^(2,N)finite_pow) ** (hermitian_matrix A:complex^(2,N)finite_pow^(2,N)finite_pow) ** A ** B:complex^(2,N)finite_pow^(2,N)finite_pow = hermitian_matrix B **
(hermitian_matrix A ** A) ** B:complex^(2,N)finite_pow^(2,N)finite_pow `SUBST1_TAC THENL[SIMP_TAC[GSYM CMATRIX_MUL_ASSOC];ALL_TAC] THEN
SUBGOAL_THEN`A ** B ** hermitian_matrix B ** hermitian_matrix A  = A ** (B ** hermitian_matrix B:complex^(2,N)finite_pow^(2,N)finite_pow)
** hermitian_matrix A:complex^(2,N)finite_pow^(2,N)finite_pow `SUBST1_TAC THENL[SIMP_TAC[GSYM CMATRIX_MUL_ASSOC];ALL_TAC] THEN
ASM_SIMP_TAC[IDCMAT_MUL_MAT]
);;

let IDCMAT_UNITARY = prove
(`unitary_matrix (id_cmatrix: complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[unitary_matrix;GSYM IDCMAT_HERMITIAN;IDCMAT_DIAGONAL;CMATRIX_MUL_DIAGONAL] THEN
SIMP_TAC[id_cmatrix;CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
COND_CASES_TAC THENL[SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let IDCMAT_MUL_QSTATE = prove
(`!q:(N)qstate. id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow ** q = q`,
GEN_TAC THEN SIMP_TAC[cmatrix_qstate_mul] THEN REWRITE_TAC[GSYM DEST_QSTATE_EQ] THEN
ASSUME_TAC (SPEC_ALL IDCMAT_UNITARY) THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY))
THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM is_qstate]) THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE))
THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;IDCMAT] THEN ONCE_REWRITE_TAC[COND_RAND] THEN ONCE_REWRITE_TAC[COND_RATOR]
THEN SIMP_TAC[COMPLEX_MUL_LID;COMPLEX_MUL_LZERO]
THEN REPEAT STRIP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG]);;

let IDCMAT_MUL_MAT = prove
(`!A:complex^(2,N)finite_pow^(2,N)finite_pow.
id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow ** A = A`,
GEN_TAC THEN SIMP_TAC[cmatrix_mul;CART_EQ;LAMBDA_BETA;IDCMAT] THEN
SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN REPEAT STRIP_TAC THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG]);;

let MAT_MUL_IDCMAT = prove
(`!A:complex^(2,N)finite_pow^(2,N)finite_pow.
A ** id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow = A`,
GEN_TAC THEN SIMP_TAC[cmatrix_mul;CART_EQ;LAMBDA_BETA;IDCMAT] THEN
SIMP_TAC[COND_RMUL;COMPLEX_MUL_RID;COMPLEX_MUL_RZERO] THEN REPEAT STRIP_TAC
THEN ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG]);;

(*Quantum gates*)
let hadamard = new_definition
  `hadamard : complex^(2,1)finite_pow^(2,1)finite_pow = lambda i j.
     if i = 1 /\ j = 1 then Cx(&1 / sqrt(&2)) else
     if i = 1 /\ j = 2 then Cx(&1 / sqrt(&2)) else
     if i = 2 /\ j = 1 then Cx(&1 / sqrt(&2)) else
     if i = 2 /\ j = 2 then --Cx(&1 / sqrt(&2)) else Cx(&0)`;;

let HADAMARD_EQ = prove
(`hadamard:complex^(2,1)finite_pow^(2,1)finite_pow = lambda i j.
        if i = 1 then Cx(&1/sqrt(&2))
               else if j = 1 then Cx(&1/sqrt(&2))
               else --Cx(&1/sqrt(&2))`,
    SIMP_TAC[hadamard;LAMBDA_BETA;CART_EQ]
    THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC
    THEN COND_CASES_TAC THENL[ASM_SIMP_TAC[];ALL_TAC] THEN
    RULE_ASSUM_TAC(SIMP_RULE[TAUT`~(p /\ q) <=> ~p \/ ~q`])
    THEN COND_CASES_TAC THENL[ASM_SIMP_TAC[];ALL_TAC] THEN
    COND_CASES_TAC THENL[ASM_SIMP_TAC[ARITH_RULE`~(2 = 1)`];ALL_TAC]
    THEN COND_CASES_TAC THENL[ASM_SIMP_TAC[ARITH_RULE`~(2 = 1)`];ALL_TAC]
    THEN RULE_ASSUM_TAC(SIMP_RULE[TAUT`~(p /\ q) <=> ~p \/ ~q`]) THEN
    POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM DE_MORGAN_THM] THEN RULE_ASSUM_TAC(
    SIMP_RULE[DIMINDEX_FINITE_POW;DIMINDEX_2;DIMINDEX_1;EXP_1]) THEN
    REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE` ~(i = 1 /\ i' = 1)
    /\ ~(i = 1 /\ i' = 2) /\ ~(i = 2 /\ i' = 1) /\ ~(i = 2 /\ i' = 2) ==>
    ~(i = 1 /\ i = 2) /\ ~(i' = 1 /\ i' = 2)`) THEN ASM_ARITH_TAC
);;

let HADAMARD_HERMITIAN = prove
(` hermitian_matrix hadamard = hadamard `,
SIMP_TAC[hermitian_matrix;hadamard] THEN
 SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
SIMP_TAC[COND_CNJ;GSYM CX_NEG;CNJ_CX] THEN MESON_TAC[]);;

let ONE_DIV_SQRT2 = prove
(`(&1 / sqrt (&2)) pow 2 = &1 / &2`,
GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[GSYM SQRT_1]
THEN SIMP_TAC[GSYM SQRT_DIV;REAL_SQRT_POW_2] THEN REAL_ARITH_TAC);;

let ONE_DIV_SQRTN = prove
(`!N. 1 <= N ==> (&1 / sqrt (&N)) pow 2 = &1 / &N`,
REPEAT STRIP_TAC THEN
GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV)[GSYM SQRT_1]
THEN SIMP_TAC[GSYM SQRT_DIV] THEN SIMP_TAC[REAL_SQRT_POW_2]
THEN SIMP_TAC[REAL_ABS_DIV] THEN SIMP_TAC[REAL_ARITH`abs(&1) = &1`]
THEN AP_TERM_TAC THEN REAL_ARITH_TAC);;

let SQRT_POW = prove
(`!n. sqrt(&2 pow n) = sqrt(&2) pow n`,
  INDUCT_TAC THENL[SIMP_TAC[real_pow;SQRT_1];ALL_TAC] THEN
  ASM_SIMP_TAC[real_pow;SQRT_MUL]);;

let HADAMARD_UNITARY = prove
(`unitary_matrix hadamard`,
SIMP_TAC[unitary_matrix;HADAMARD_HERMITIAN;cmatrix_mul;hadamard;id_cmatrix]
THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;COND_LMUL;COND_RMUL] THEN
SIMP_TAC[COMPLEX_MUL_LZERO;COMPLEX_MUL_RZERO;COMPLEX_MUL_RNEG;COMPLEX_NEG_0;COMPLEX_MUL_LNEG;COMPLEX_NEG_MUL2]
THEN SIMP_TAC[COND_ID;GSYM CX_MUL;GSYM REAL_POW_2;ONE_DIV_SQRT2;SQRT_1] THEN
SIMP_TAC[REAL_ARITH`(&1 / &1) pow 1= &1`] THEN SIMP_TAC[REAL_ARITH`(&1 / &1) = &1`] THEN
SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;DIMINDEX_1;ARITH_RULE`2 EXP 1 = 2`;VSUM_2]
THEN ONCE_SIMP_TAC[FORALL_2;COND_CLAUSES] THEN ONCE_SIMP_TAC[FORALL_2;COND_CLAUSES]
THEN ONCE_SIMP_TAC[COND_T_F;COND_RIGHT_F] THEN SIMP_TAC[COND_T_F;COND_RIGHT_F]
THEN SIMP_TAC[COND_RAND;COND_RATOR] THEN SIMP_TAC[GSYM CX_ADD;REAL_ARITH`&1 / &2  + &1/ &2 = &1`]
THEN SIMP_TAC[REAL_ARITH`&1 / &1  + &1/ &1 = &2`] THEN
SIMP_TAC[GSYM CX_NEG;GSYM CX_ADD;REAL_ARITH`&1 / &2 + -- (&1/ &2) = &0`]
THEN MESON_TAC[]);;

(* to prove n hadamard unitary*)
let OFFSET_IMAGE = prove
(`!c m:num. {k |k IN c + 1..c + m /\ P k}  = IMAGE(\x.x + c) {k | k IN 1..m /\ P (k + c)}`,
REPEAT GEN_TAC THEN
SIMP_TAC[IN_NUMSEG;ARITH_RULE`c+1 <= k /\ k <= c+m <=> 1 <= k - c /\ k - c <= m`]
THEN SIMP_TAC[IN_ELIM_THM;EXTENSION;IN_NUMSEG;IN_IMAGE] THEN
GEN_TAC THEN EQ_TAC THENL[REPEAT STRIP_TAC THEN EXISTS_TAC`x - c:num`
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x-c ==>x- c + c = x`];ALL_TAC]
THEN STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`(x' + c) - c:num  =  x'`]);;

let CARD_IMAGE_EQ = prove
(`!s c:num.FINITE s ==> CARD(IMAGE (\x. x + c) s) = CARD s`,
REPEAT STRIP_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN
ASM_SIMP_TAC[] THEN MESON_TAC[ARITH_RULE`x + c:num = y + c ==> x = y`]);;

let POW_REFL = prove
(`&2 pow dimindex (:N) / &2 pow dimindex (:N) = &1`,
ASSUME_TAC REAL_POW_LT THEN
FIRST_X_ASSUM (ASSUME_TAC o SPECL[`&2`;`dimindex(:N)`]) THEN
RULE_ASSUM_TAC(SIMP_RULE[REAL_ARITH`&0 < &2`]) THEN
ASM_SIMP_TAC[REAL_FIELD`&0 < a ==> a / a = &1`]);;

let BITSET_ADD = prove
(`!k n:num. k < 2 EXP n ==> bitset (k + 2 EXP n) = bitset (k) UNION {n}`,
REPEAT GEN_TAC THEN STRIP_TAC THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN
ASSUME_TAC (SPEC`n:num` (GSYM BITS_OF_NUM_POW2)) THEN
SUBGOAL_THEN`DISJOINT (bits_of_num k) {n:num}` ASSUME_TAC
THENL [SIMP_TAC[DISJOINT_SING] THEN UNDISCH_TAC`k < 2 EXP n`
THEN SIMP_TAC[GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN
SIMP_TAC[SUBSET;IN_ELIM_THM] THEN MESON_TAC[LT_REFL];ALL_TAC]
THEN POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[BITS_OF_NUM_ADD;BITSET_EQ_BITSNUM]);;

let BITS_OF_NUM_1 = prove
 (`bits_of_num 1 = {0}`,
  REWRITE_TAC[GSYM BITS_OF_NUM_POW2; EXP]);;

let bitand = new_definition
`!a b:num. bitand a b = (bitset a) INTER (bitset b)`;;

let BITAND_0 = prove
(`!a:num. CARD(bitand a 0) = 0 /\
CARD(bitand 0 a) = 0`,
SIMP_TAC[bitand;BITSET_0;INTER_EMPTY;CARD_CLAUSES]);;

let BITAND_SYM = prove
(`!a b:num. bitand a b = bitand b a`,
SIMP_TAC[bitand] THEN SET_TAC[]);;

let BITAND_ODD_CARD = prove
(`!N c:num.
  0 < c /\ c < 2 EXP N /\ 0 < N ==> CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1)))} = 2 EXP (N -1)`,
INDUCT_TAC THENL[ARITH_TAC;ALL_TAC]
 THEN REPEAT STRIP_TAC THEN POP_ASSUM MP_TAC
THEN SIMP_TAC[ARITH_RULE`0 < SUC N`] THEN
SIMP_TAC[EXP;bitand;ARITH_RULE`2 * 2 EXP N = 2 EXP N + 2 EXP N`]
THEN ASSUME_TAC(ARITH_RULE`1 <= (2 EXP N) + 1 /\ 2 EXP N <= 2 EXP N + 2 EXP N`)
THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPECL[`1`;`2 EXP N`;`2 EXP N + 2 EXP N`] (GSYM NUMSEG_COMBINE_R)))
THEN ASM_SIMP_TAC[UNION_RESTRICT] THEN SUBGOAL_THEN`{k | k IN 1..2 EXP N /\ ODD (CARD (bitset c INTER bitset (k - 1)))}
  INTER {k | k IN 2 EXP N + 1..2 EXP N + 2 EXP N /\
             ODD (CARD (bitset c INTER bitset (k - 1)))} = {}`ASSUME_TAC
THENL[SUBGOAL_THEN`2 EXP N < 2 EXP N + 1 ==> DISJOINT(1..2 EXP N) (2 EXP N + 1..2 EXP N + 2 EXP N)`ASSUME_TAC
 THENL [MESON_TAC[GSYM DISJOINT_NUMSEG];ALL_TAC] THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`2 EXP N < 2 EXP N +1`]) THEN
ASM_SIMP_TAC[GSYM DISJOINT;SET_RULE `DISJOINT s t ==> DISJOINT {x | x IN s /\ P x} {x | x IN t /\ P x}`];ALL_TAC]
THEN ASM_SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;CARD_UNION] THEN
SIMP_TAC[OFFSET_IMAGE;FINITE_NUMSEG;FINITE_RESTRICT;CARD_IMAGE_EQ] THEN
SIMP_TAC[IN_NUMSEG] THEN SUBGOAL_THEN `{k | (1 <= k /\ k <= 2 EXP N) /\
          ODD (CARD (bitset c INTER bitset ((k + 2 EXP N) - 1)))} =
          {k | (1 <= k /\ k <= 2 EXP N) /\
          ODD (CARD (bitset c INTER bitset ((k - 1) + 2 EXP N)))} `SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN
POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> (x + 2 EXP N) - 1 = x - 1 + 2 EXP N`];
ALL_TAC] THEN STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> (x + 2 EXP N) - 1 = x - 1 + 2 EXP N`];
ALL_TAC] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (CARD (bitset c INTER bitset (k - 1 + 2 EXP N)))} = {k | (1 <= k /\ k <= 2 EXP N) /\
  ODD (CARD (bitset c INTER (bitset (k - 1) UNION {N})))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL [STRIP_TAC THEN ASM_SIMP_TAC[] THEN
MP_TAC (SPECL[`x-1`;`N:num`] BITSET_ADD) THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x /\ x <= 2 EXP N ==> x - 1 < 2 EXP N`]
THEN STRIP_TAC THEN UNDISCH_TAC`ODD (CARD (bitset c INTER bitset (x - 1 + 2 EXP N)))` THEN
ASM_SIMP_TAC[];ALL_TAC] THEN STRIP_TAC THEN MP_TAC (SPECL[`x-1`;`N:num`] BITSET_ADD) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= x /\ x <= 2 EXP N ==> x - 1 < 2 EXP N`];ALL_TAC] THEN
SIMP_TAC[UNION_OVER_INTER;ARITH_RULE`SUC N - 1 = N`] THEN ASM_CASES_TAC` c < 2 EXP N /\0 < N`
THENL[FIRST_X_ASSUM(MP_TAC o SPEC`c:num`) THEN ASM_SIMP_TAC[IN_NUMSEG;bitand;BITSET_EQ_BITSNUM]
THEN ASSUME_TAC(SPEC`c:num` BITS_OF_NUM_SUBSET_NUMSEG_LT) THEN
SUBGOAL_THEN`bits_of_num c INTER {N} = {}`SUBST1_TAC THENL[POP_ASSUM MP_TAC
THEN UNDISCH_TAC`c < 2 EXP N /\ 0 < N` THEN REPEAT STRIP_TAC THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[GSYM DISJOINT] THEN SIMP_TAC[DISJOINT_SING] THEN
MP_TAC(SPECL[`c:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))THEN
ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;ARITH_RULE`(a:num) + a = 2 * a`] THEN
GEN_REWRITE_TAC(RAND_CONV o LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[ARITH_RULE`2 = (2 EXP 1)`]
THEN ASM_SIMP_TAC[GSYM EXP_ADD;ARITH_RULE`0 < N ==> 1 + N - 1 = N`];ALL_TAC]
THEN UNDISCH_TAC`~(c < 2 EXP N /\ 0 < N)` THEN SIMP_TAC[DE_MORGAN_THM;ARITH_RULE`~(a < b:num) <=> b <= a`]
THEN ONCE_SIMP_TAC[TAUT`P \/ Q <=> Q \/ P`] THEN STRIP_TAC
THENL[RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`N <= 0 <=> N = 0`])
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN ASM_SIMP_TAC[EXP;ARITH] THEN UNDISCH_TAC`0 < c`
THEN SIMP_TAC[GSYM IMP_CONJ;ARITH_RULE`0 < c /\ c < 2 <=> c = 1`] THEN
SIMP_TAC[GSYM IN_NUMSEG;NUMSEG_SING;IN_SING]
THEN ONCE_REWRITE_TAC[SET_RULE `{x | x = a /\ P x} = {x | x = a /\ P a}`]
THEN SIMP_TAC[ARITH;BITSET_0] THEN SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_1;INTER_EMPTY]
THEN SIMP_TAC[INTER_IDEMPOT;CARD_SING;CARD_CLAUSES;UNION_EMPTY] THEN SIMP_TAC[ODD;ARITH_RULE`ODD 1 <=> T`]
THEN SIMP_TAC[SET_RULE `{k |k = a} = {a:num}`;CARD_SING;SET_RULE`{k | F} = {}`;CARD_CLAUSES;ARITH];ALL_TAC]
THEN FIRST_X_ASSUM(MP_TAC o SPEC`c - 2 EXP N `) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N  <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;bitand;IN_NUMSEG] THEN
POP_ASSUM MP_TAC THEN SIMP_TAC[ARITH_RULE`2 EXP N <= c <=> 2 EXP N < c \/ 2 EXP N = c`]
THEN STRIP_TAC THENL[ASM_CASES_TAC`~(0 < N)` THENL[RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`~(0 < N) <=> N = 0`])
THEN ASM_SIMP_TAC[ARITH;GSYM IN_NUMSEG;NUMSEG_SING;IN_SING] THEN UNDISCH_TAC`2 EXP N < c`
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN ASM_SIMP_TAC[EXP;ARITH] THEN SIMP_TAC[GSYM IMP_CONJ]
THEN SIMP_TAC[ARITH_RULE`c < 2 /\ 1 < c <=> F`];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[TAUT`~ ~ P <=> P`])
THEN ASM_SIMP_TAC[] THEN ASSUME_TAC(SPECL[`c - 2 EXP N`;`N:num`] BITSET_ADD) THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`c - 2 EXP N  < 2 EXP N  <=> c < 2 EXP N + 2 EXP N`]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD])
THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`1 + N = SUC N`]) THEN POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}`
THEN SUBGOAL_THEN`bitset (c - 2 EXP N + 2 EXP N) = bitset c`SUBST1_TAC THENL
[ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`];ALL_TAC] THEN
STRIP_TAC THEN SUBGOAL_THEN`bitset c INTER {N} = {N}`ASSUME_TAC THENL
[SIMP_TAC[INTER;IN_ELIM_THM;EXTENSION] THEN ASM_SIMP_TAC[IN_UNION] THEN
SET_TAC[];ALL_TAC] THEN POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN STRIP_TAC THEN
SIMP_TAC[UNION_COMM;INTER_OVER_UNION] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[UNION_COMM]
THEN SIMP_TAC[SET_RULE`s UNION s UNION t = s UNION t`] THEN
GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[INTER_COMM]
THEN GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o DEPTH_CONV)[UNION_OVER_INTER]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD
      (bitset (k - 1) INTER {N} UNION
       bitset (k - 1) INTER bitset (c - 2 EXP N)))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD(bitset (c - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`ASSUME_TAC
THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC] THEN
SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`SUBST1_TAC THENL
[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC]
THEN ASM_SIMP_TAC[] THEN UNDISCH_TAC`bitset c = bitset (c - 2 EXP N) UNION {N}` THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[UNION_COMM]
THEN STRIP_TAC THEN ASM_SIMP_TAC[UNION_OVER_INTER] THEN
POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN SIMP_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN SIMP_TAC[UNION_OVER_INTER]
THEN STRIP_TAC THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD({N} UNION bitset (k - 1) INTER {N} UNION
       bitset (k - 1) INTER bitset (c - 2 EXP N)))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD({N} UNION bitset (k - 1) INTER bitset (c - 2 EXP N)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`ASSUME_TAC
THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC] THEN
SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`SUBST1_TAC THENL
[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY];ALL_TAC]
THEN SIMP_TAC[INTER_COMM] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (CARD ({N} UNION bitset (c - 2 EXP N) INTER bitset (k - 1)))}
  = {k | (1 <= k /\ k <= 2 EXP N) /\
  ODD(CARD {N}  + CARD(bitset (c - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC
THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < c` THEN
SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_SING] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (1 + CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)))}  =
  {k | (1 <= k /\ k <= 2 EXP N) /\
      EVEN (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN AP_TERM_TAC
THEN SIMP_TAC[ARITH_RULE`1 + a = SUC a`] THEN SIMP_TAC[ODD;NOT_ODD];ALL_TAC]
THEN SIMP_TAC[GSYM IN_NUMSEG] THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM IN_NUMSEG])
THEN SUBGOAL_THEN `{k |k IN 1.. 2 EXP N /\ EVEN (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)))}
= (1..2 EXP N) DIFF {k |k IN 1..2 EXP N /\ ODD (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)))}`
SUBST1_TAC THENL[SET_TAC[NOT_ODD];ALL_TAC] THEN SIMP_TAC[CARD_DIFF;FINITE_NUMSEG;SUBSET;IN_ELIM_THM]
THEN SIMP_TAC[CARD_NUMSEG_1] THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN`2 EXP (N - 1) < 2 EXP N`ASSUME_TAC
THENL[SIMP_TAC[LT_EXP;ARITH] THEN ASM_SIMP_TAC[ARITH_RULE`0 < N ==> N - 1 < N`];ALL_TAC]
THEN  POP_ASSUM MP_TAC THEN SIMP_TAC[ARITH_RULE`2 EXP (N - 1) < 2 EXP N ==> 2 EXP (N - 1)
  + 2 EXP N - 2 EXP (N - 1) = 2 EXP N`];ALL_TAC] THEN
RULE_ASSUM_TAC(SIMP_RULE[EQ_SYM_EQ]) THEN POP_ASSUM MP_TAC THEN POP_ASSUM (K ALL_TAC)
THEN POP_ASSUM (K ALL_TAC) THEN SIMP_TAC[ARITH;LT_REFL] THEN
SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2] THEN STRIP_TAC THEN
SIMP_TAC[INTER_IDEMPOT;UNION_COMM] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
          ODD   (CARD ({N} INTER bits_of_num (k - 1)))}  =
    {k | (1 <= k /\ k <= 2 EXP N) /\
            ODD (CARD {})}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL
[STRIP_TAC THEN ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bitset (x - 1)  = {}`ASSUME_TAC THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM;INTER_EMPTY]
THEN SIMP_TAC[CARD_CLAUSES];ALL_TAC] THEN STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SIMP_TAC[CARD_CLAUSES;ODD];ALL_TAC]
THEN SIMP_TAC[CARD_CLAUSES;ODD;SET_RULE`{k | F} = {}`]
 THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (CARD ({N} UNION {N} INTER bits_of_num (k - 1)))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD (CARD ({N} UNION {}))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC
THENL [STRIP_TAC THEN ASM_SIMP_TAC[] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;ARITH];ALL_TAC]
THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;ARITH];ALL_TAC]
THEN SIMP_TAC[UNION_EMPTY;CARD_SING;ARITH;GSYM IN_NUMSEG;CARD_NUMSEG_1]
THEN SIMP_TAC[ADD_SYM;ADD_0] THEN SIMP_TAC[IN_NUMSEG] THEN SUBGOAL_THEN`{k | 1 <= k /\ k <= 2 EXP N} =
  1..2 EXP N`SUBST1_TAC THENL[REWRITE_TAC[EXTENSION; IN_NUMSEG; IN_ELIM_THM];ALL_TAC]
THEN SIMP_TAC[CARD_NUMSEG_1]);;

let BITAND_CARD_ODD_EQ_EVEN = prove
(`!N c:num.
  0 < c /\ c < 2 EXP N /\ 0 < N ==> CARD {k | k IN 1..2 EXP N /\
       ODD (CARD (bitand c (k - 1)))} =
       CARD {k | k IN 1..2 EXP N /\ EVEN (CARD (bitand c (k - 1)))}`,
SIMP_TAC[BITAND_ODD_CARD] THEN REPEAT STRIP_TAC THEN
SUBGOAL_THEN `{k |k IN 1.. 2 EXP N /\ EVEN (CARD (bitand c (k - 1)))}
= (1..2 EXP N) DIFF {k |k IN 1..2 EXP N /\ ODD (CARD (bitand c (k - 1)))}`SUBST1_TAC
THENL[SET_TAC[NOT_ODD];ALL_TAC] THEN SIMP_TAC[CARD_DIFF;FINITE_NUMSEG;SUBSET;IN_ELIM_THM;CARD_NUMSEG_1]
THEN ASM_SIMP_TAC[BITAND_ODD_CARD] THEN SIMP_TAC[ARITH_RULE`a:num = b - a <=> a + a = b`;GSYM MULT_2]
THEN SIMP_TAC[GSYM (SPECL[`2`;`N - 1`](CONJUNCT2 EXP))] THEN AP_TERM_TAC THEN ASM_ARITH_TAC);;

let BITSET_3 = prove
(`bits_of_num 3 = {0,1}`,
SIMP_TAC[ARITH_RULE`3 = 1 + 2`;SET_RULE`{0,1} = {0} UNION {1}`] THEN
SIMP_TAC[GSYM BITS_OF_NUM_POW2;EXP;ARITH_RULE`2 EXP 1 = 2`] THEN
 MATCH_MP_TAC BITS_OF_NUM_ADD THEN SIMP_TAC[BITS_OF_NUM_1] THEN
 ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`] THEN REWRITE_TAC[BITS_OF_NUM_POW2] THEN
 SIMP_TAC[DISJOINT;INTER;IN_ELIM_THM;EXTENSION;IN_SING] THEN SET_TAC[ARITH_RULE`~(0 = 1)`]);;

let INTER_EMPTY_0_1 = prove
(`{0} INTER {1} = {}`,
SIMP_TAC[INTER;EXTENSION;IN_ELIM_THM;IN_SING] THEN SET_TAC[ARITH_RULE`~(0 = 1)`]);;

let CARD_2 = prove
(`CARD{0,1} = 2`,
ASSUME_TAC(SET_RULE`{0} UNION {1} = {0,1}`) THEN ASSUME_TAC INTER_EMPTY_0_1 THEN
SUBGOAL_THEN`CARD{0,1} = CARD{0} + CARD{1}`SUBST1_TAC THENL[MATCH_MP_TAC (GSYM CARD_UNION_EQ) THEN
ASM_SIMP_TAC[] THEN ASSUME_TAC(SPECL[`0`;`1`] numseg) THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`0 <= x /\ x <= 1
<=> x = 0 \/ x = 1`]) THEN RULE_ASSUM_TAC(SIMP_RULE[SET_RULE`{x |x = 0 \/ x = 1} = {0} UNION {1}`])
THEN SIMP_TAC[SET_RULE`{0,1} = {0} UNION {1}`] THEN POP_ASSUM MP_TAC THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[FINITE_NUMSEG];ALL_TAC]
THEN SIMP_TAC[CARD_SING;ARITH]);;

let BITAND_ODD_ODD_CARD = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`,
INDUCT_TAC THENL[ARITH_TAC;ALL_TAC] THEN REPEAT STRIP_TAC THEN
UNDISCH_TAC`!c d.
          0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d)
          ==> CARD
              {k | k IN 1..2 EXP N /\
                   ODD (CARD (bitand c (k - 1))) /\
                   ODD (CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`
 THEN SIMP_TAC[GSYM ODD_MULT] THEN
ASSUME_TAC(ARITH_RULE`1 <= (2 EXP N) + 1 /\ 2 EXP N <= 2 EXP N + 2 EXP N`)
THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPECL[`1`;`2 EXP N`;`2 EXP N + 2 EXP N`] (GSYM NUMSEG_COMBINE_R)))
THEN ASM_SIMP_TAC[UNION_RESTRICT;EXP;MULT_2] THEN POP_ASSUM (K ALL_TAC) THEN
SUBGOAL_THEN`DISJOINT {k | k IN 1..2 EXP N /\
               ODD (CARD (bitand c (k - 1)) * CARD (bitand d (k - 1)))}
   {k | k IN 2 EXP N + 1..2 EXP N + 2 EXP N /\
           ODD (CARD (bitand c (k - 1)) * CARD (bitand d (k - 1)))}`ASSUME_TAC
THENL[SUBGOAL_THEN`2 EXP N < 2 EXP N + 1 ==> DISJOINT(1..2 EXP N) (2 EXP N + 1..2 EXP N + 2 EXP N)`ASSUME_TAC
THENL[MESON_TAC[GSYM DISJOINT_NUMSEG];ALL_TAC] THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`2 EXP N < 2 EXP N +1`])
THEN ASM_SIMP_TAC[GSYM DISJOINT;SET_RULE `DISJOINT s t ==> DISJOINT {x | x IN s /\ P x} {x | x IN t /\ P x}`];
ALL_TAC] THEN RULE_ASSUM_TAC(SIMP_RULE[DISJOINT]) THEN ASM_SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;CARD_UNION]
THEN SIMP_TAC[OFFSET_IMAGE;FINITE_NUMSEG;FINITE_RESTRICT;CARD_IMAGE_EQ] THEN SIMP_TAC[IN_NUMSEG] THEN STRIP_TAC
THEN SUBGOAL_THEN `{k | (1 <= k /\ k <= 2 EXP N) /\ ODD(CARD (bitand c ((k + 2 EXP N) - 1)) *
       CARD (bitand d ((k + 2 EXP N) - 1)))} =
          {k | (1 <= k /\ k <= 2 EXP N) /\ ODD(CARD (bitand c (k - 1 + 2 EXP N )) *
       CARD (bitand d (k - 1 + 2 EXP N )))} `SUBST1_TAC THENL
[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL
[STRIP_TAC THEN
POP_ASSUM MP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> (x + 2 EXP N) - 1 = x - 1 + 2 EXP N`];ALL_TAC]
THEN STRIP_TAC THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> (x + 2 EXP N) - 1 = x - 1 + 2 EXP N`];ALL_TAC]
THEN SIMP_TAC[bitand] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset c INTER bitset (k - 1 + 2 EXP N)) *
       CARD (bitset d INTER bitset (k - 1 + 2 EXP N)))} = {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset c INTER (bitset (k - 1) UNION {N})) *
       CARD (bitset d INTER (bitset (k - 1) UNION {N})))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[] THEN
MP_TAC (SPECL[`x-1`;`N:num`] BITSET_ADD) THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x /\ x <= 2 EXP N ==> x - 1 < 2 EXP N`]
THEN STRIP_TAC THEN UNDISCH_TAC`ODD
      (CARD   (bitset c INTER bitset (x - 1 + 2 EXP N)) *
         CARD (bitset d INTER bitset (x - 1 + 2 EXP N)))`
THEN ASM_SIMP_TAC[];ALL_TAC] THEN STRIP_TAC THEN MP_TAC (SPECL[`x-1`;`N:num`] BITSET_ADD) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= x /\ x <= 2 EXP N ==> x - 1 < 2 EXP N`];ALL_TAC] THEN
SIMP_TAC[UNION_OVER_INTER;ARITH_RULE`SUC N - 2 = N - 1`] THEN ASM_CASES_TAC` c < 2 EXP N /\ 1 < N /\ d < 2 EXP N`
THENL[FIRST_X_ASSUM(MP_TAC o SPECL[`c:num`;`d:num`]) THEN ASM_SIMP_TAC[bitand;BITSET_EQ_BITSNUM]
THEN ASSUME_TAC(SPEC`c:num` BITS_OF_NUM_SUBSET_NUMSEG_LT) THEN ASSUME_TAC(SPEC`d:num` BITS_OF_NUM_SUBSET_NUMSEG_LT)
THEN SUBGOAL_THEN`bits_of_num c INTER {N} = {}`SUBST1_TAC THENL[POP_ASSUM MP_TAC THEN
UNDISCH_TAC`c < 2 EXP N /\ 1 < N /\ d < 2 EXP N` THEN REPEAT STRIP_TAC THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[GSYM DISJOINT] THEN MP_TAC(SPECL[`c:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`bits_of_num d INTER {N} = {}`SUBST1_TAC
THENL[POP_ASSUM MP_TAC THEN UNDISCH_TAC`c < 2 EXP N /\ 1 < N /\ d < 2 EXP N` THEN REPEAT STRIP_TAC
THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[GSYM DISJOINT] THEN
MP_TAC(SPECL[`d:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;GSYM MULT_2]
THEN GEN_REWRITE_TAC(RAND_CONV o LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[ARITH_RULE`2 = (2 EXP 1)`]
THEN ASM_SIMP_TAC[GSYM EXP_ADD] THEN UNDISCH_TAC`1 < SUC N` THEN
SIMP_TAC[ARITH_RULE`1 < SUC N <=> 0 < N`;ARITH_RULE`1 + N - 2 = 1 + N - 1 - 1`] THEN REPEAT STRIP_TAC THEN
AP_TERM_TAC THEN ASM_ARITH_TAC;ALL_TAC] THEN UNDISCH_TAC`~(c < 2 EXP N /\ 1 < N /\ d < 2 EXP N)` THEN
SIMP_TAC[DE_MORGAN_THM;ARITH_RULE`~(a < b:num) <=> b <= a`] THEN ASM_CASES_TAC`N <= 1` THENL[
ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`1 < SUC N <=> 0 < N `]) THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`N <= 1 <=> N = 0 \/ N = 1`]) THEN POP_ASSUM MP_TAC THEN
ASM_SIMP_TAC[ARITH_RULE`0 < N ==> ~(N = 0)`;ARITH] THEN STRIP_TAC THEN
SIMP_TAC[ARITH_RULE`1 <= k /\ k <= 2 <=> k = 1 \/ k = 2`] THEN
SIMP_TAC[SET_RULE `{x | (x = a \/ x = b) /\ P x} = {x | x = a /\ P a \/  x = b /\ P b}`]
THEN SIMP_TAC[ARITH;BITSET_0] THEN SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_1;INTER_EMPTY;CARD_CLAUSES;UNION_EMPTY]
THEN SIMP_TAC[ODD;MULT_0] THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`d < 2 EXP SUC N` THEN
ASM_SIMP_TAC[ARITH] THEN REPEAT STRIP_TAC THEN
MP_TAC (ARITH_RULE `0 < c /\ c < 4 ==> (c = 1 \/ c = 2 \/ c = 3)`) THEN
MP_TAC (ARITH_RULE `0 < d /\ d < 4 ==> (d = 1 \/ d = 2 \/ d = 3)`) THEN ASM_SIMP_TAC[] THEN
ASM_CASES_TAC`d = 1` THENL[ASM_SIMP_TAC[BITS_OF_NUM_1] THEN SIMP_TAC[INTER_IDEMPOT;CARD_SING] THEN
MP_TAC (ARITH_RULE`~(c = d) /\ d = 1 ==> ~(c = 1)`) THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN
SIMP_TAC[INTER_OVER_UNION;UNION_IDEMPOT;SET_RULE`{0} UNION {1} = {0,1}`;SET_RULE`{0} INTER {0,1} = {0}`;CARD_SING]
THEN ASM_CASES_TAC`c = 2` THENL[ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`] THEN
SIMP_TAC[BITS_OF_NUM_POW2] THEN SIMP_TAC[SET_RULE`{1} INTER {0} UNION {1} = {1} UNION {1} INTER {0}`;
INTER_IDEMPOT;INTER_OVER_UNION;UNION_IDEMPOT] THEN SIMP_TAC[SET_RULE`{1} UNION {0} = {0,1}`;SET_RULE`{1} INTER {0,1} = {1}`;
CARD_SING;ARITH] THEN SUBGOAL_THEN`{0} INTER {1} = {}`ASSUME_TAC THENL[SET_TAC[ARITH_RULE`~( 0 = 1)`];ALL_TAC] THEN
GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV) [INTER_COMM] THEN ASM_SIMP_TAC[CARD_CLAUSES;ARITH]
THEN SIMP_TAC[SET_RULE`{k |F} = {}`;CARD_CLAUSES] THEN SIMP_TAC[SET_RULE`{k |k = 2} = {2}`;CARD_SING;ARITH];ALL_TAC]
THEN ASM_SIMP_TAC[BITSET_3] THEN SIMP_TAC[SET_RULE`{0,1} INTER {0} = {0}`;SET_RULE`{0} UNION {0,1} = {0,1}`]
THEN SIMP_TAC[SET_RULE`{0,1} INTER {1} = {1}`;SET_RULE`{0} UNION {1} = {0,1}`] THEN SIMP_TAC[INTER_IDEMPOT;CARD_SING;ARITH]
THEN SIMP_TAC[CARD_2;INTER_EMPTY_0_1;CARD_CLAUSES;ARITH;SET_RULE`{k |F} = {}`;SET_RULE`{k | k = 2} = {2}`;CARD_SING];ALL_TAC]
THEN ASM_SIMP_TAC[] THEN ASM_CASES_TAC`d = 2` THENL[ASM_SIMP_TAC[] THEN MP_TAC(ARITH_RULE`~(c = d) /\ d = 2 ==> ~(c = 2)`)
THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN ASM_CASES_TAC`c = 1` THENL[ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`]
THEN SIMP_TAC[BITS_OF_NUM_POW2;BITS_OF_NUM_1;INTER_IDEMPOT;INTER_EMPTY_0_1] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
SIMP_TAC[INTER_EMPTY_0_1;UNION_EMPTY;CARD_SING;CARD_CLAUSES;ARITH] THEN SIMP_TAC[SET_RULE`{k | F} = {}`;SET_RULE`{k | k = 2} = {2}`;CARD_SING;CARD_CLAUSES;ARITH];ALL_TAC] THEN ASM_SIMP_TAC[BITSET_3] THEN
SIMP_TAC[SET_RULE`{0,1} INTER {0} = {0}`;SET_RULE`{0,1} INTER {1} = {1}`] THEN ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`]
THEN REWRITE_TAC[BITS_OF_NUM_POW2] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
SIMP_TAC[INTER_EMPTY_0_1;INTER_IDEMPOT;SET_RULE`{0} UNION {1} = {0,1}`;CARD_2;CARD_SING;CARD_CLAUSES;ARITH;UNION_EMPTY]
THEN SIMP_TAC[SET_RULE`{k |F} = {}`;SET_RULE`{k |k = 1} = {1}`;CARD_SING;CARD_CLAUSES;ARITH];ALL_TAC] THEN
ASM_SIMP_TAC[BITSET_3] THEN MP_TAC(ARITH_RULE`~(c = d) /\ d = 3 ==> ~(c = 3)`) THEN ASM_SIMP_TAC[] THEN
ASM_CASES_TAC`c = 1` THENL[ASM_SIMP_TAC[BITS_OF_NUM_1] THEN
SIMP_TAC[INTER_IDEMPOT;INTER_EMPTY_0_1;SET_RULE`{0,1} INTER {0} = {0}`;SET_RULE`{0,1} INTER {1} = {1}`;UNION_EMPTY] THEN
SIMP_TAC[SET_RULE`{0} UNION {1} = {0,1}`;CARD_2;CARD_SING;CARD_CLAUSES;SET_RULE`{k |F} = {}`;SET_RULE`{k |k = 2} = {2}`;ARITH];
ALL_TAC] THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[ARITH_RULE`2 = 2 EXP 1`] THEN SIMP_TAC[BITS_OF_NUM_POW2;INTER_IDEMPOT] THEN
ONCE_REWRITE_TAC[INTER_COMM] THEN SIMP_TAC[INTER_EMPTY_0_1;UNION_EMPTY;SET_RULE`{0} INTER {0,1} = {0}`;SET_RULE`{1} INTER {0,1} = {1}`]
THEN SIMP_TAC[SET_RULE`{0} UNION {1} = {0,1}`;CARD_SING;CARD_2;CARD_CLAUSES;ARITH;SET_RULE`{k |F} = {}`;SET_RULE`{k |k = 1} = {1}`];
ALL_TAC] THEN ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`~(N <= 1) <=> 1 < N`]) THEN STRIP_TAC THENL[
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`2 EXP N <= c <=> 2 EXP N < c \/ c = 2 EXP N`]) THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] BITSET_ADD)
THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] BITSET_ADD) THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`]
THEN REPEAT STRIP_TAC THEN UNDISCH_TAC`2 EXP N < c \/ c = 2 EXP N` THEN
STRIP_TAC THENL[FIRST_X_ASSUM(MP_TAC o SPECL[`c - 2 EXP N `;`d - 2 EXP N`])
THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`]
THEN ASM_CASES_TAC`2 EXP N < d`
THENL[ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c /\ 2 EXP N < d /\ ~(c = d) ==> ~(c - 2 EXP N = d - 2 EXP N)`]
THEN UNDISCH_TAC`bitset (d - 2 EXP N + 2 EXP N) = bitset (d - 2 EXP N) UNION {N}` THEN
SUBGOAL_THEN`bitset (d - 2 EXP N + 2 EXP N) = bitset d`SUBST1_TAC THENL[
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < n ==> n - 2 EXP N + 2 EXP N = n`];ALL_TAC] THEN STRIP_TAC THEN
UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}` THEN
SUBGOAL_THEN`bitset (c - 2 EXP N + 2 EXP N) = bitset c`SUBST1_TAC THENL[
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < n ==> n - 2 EXP N + 2 EXP N = n`];ALL_TAC] THEN STRIP_TAC
THEN SUBGOAL_THEN`bitset c INTER {N} = {N}`ASSUME_TAC THENL[SIMP_TAC[INTER;IN_ELIM_THM;EXTENSION]
THEN ASM_SIMP_TAC[IN_UNION] THEN SET_TAC[];ALL_TAC] THEN SUBGOAL_THEN`bitset d INTER {N} = {N}`ASSUME_TAC
THENL[SIMP_TAC[INTER;IN_ELIM_THM;EXTENSION] THEN ASM_SIMP_TAC[IN_UNION] THEN SET_TAC[];ALL_TAC]
THEN POP_ASSUM MP_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
SIMP_TAC[UNION_COMM;INTER_OVER_UNION] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[UNION_COMM] THEN
SIMP_TAC[SET_RULE`s UNION s UNION t = s UNION t`] THEN RULE_ASSUM_TAC(SIMP_RULE[EQ_SYM_EQ;UNION_COMM])
THEN UNDISCH_TAC`{N} UNION bitset (d - 2 EXP N) = bitset d` THEN
UNDISCH_TAC`{N} UNION bitset (c - 2 EXP N) = bitset c` THEN SIMP_TAC[] THEN
REPEAT STRIP_TAC THEN RULE_ASSUM_TAC(ONCE_REWRITE_RULE[EQ_SYM_EQ])
THEN RULE_ASSUM_TAC(SIMP_RULE[bitand]) THEN
ASM_SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD({N} INTER bitset (k - 1) UNION
bitset (c - 2 EXP N) INTER bitset (k - 1)) * CARD({N} INTER bitset (k - 1) UNION
            bitset (d - 2 EXP N) INTER bitset (k - 1)))} =
    {k | (1 <= k /\ k <= 2 EXP N) /\ ODD(CARD(bitset (c - 2 EXP N) INTER bitset (k - 1)) *
    CARD( bitset (d - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM]
THEN GEN_TAC THEN EQ_TAC THENL [STRIP_TAC THEN ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bitset (x - 1) = {}`SUBST1_TAC
    THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC] THEN SIMP_TAC[]
THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bitset (x - 1) = {}`SUBST1_TAC THENL[
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;INTER_COMM];ALL_TAC] THEN
UNDISCH_TAC`2 EXP (N - 2) =  CARD
      { k | (1 <= k /\ k <= 2 EXP N) /\
             ODD
             (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)) *
              CARD (bitset (d - 2 EXP N) INTER bitset (k - 1)))}`
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV) [EQ_SYM_EQ] THEN SIMP_TAC[]
THEN SIMP_TAC[UNION_OVER_INTER;INTER_IDEMPOT]
THEN ONCE_REWRITE_TAC[SET_RULE`(s UNION t) UNION u UNION v = (s UNION u) UNION t UNION v`]
THEN STRIP_TAC THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD(({N} UNION bitset (c - 2 EXP N) INTER {N}) UNION
        {N} INTER bitset (k - 1) UNION  bitset (c - 2 EXP N) INTER bitset (k - 1)) *
       CARD(({N} UNION bitset (d - 2 EXP N) INTER {N}) UNION
        {N} INTER bitset (k - 1) UNION  bitset (d - 2 EXP N) INTER bitset (k - 1)))} =
        {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD ({N} UNION bitset (c - 2 EXP N) INTER bitset (k - 1) ) *
       CARD({N} UNION bitset (d - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bitset (x - 1) = {}`SUBST1_TAC
    THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY] THEN UNDISCH_TAC`bitset c INTER {N} = {N}`
THEN UNDISCH_TAC`bitset d INTER {N} = {N}` THEN ASM_SIMP_TAC[] THEN
SIMP_TAC[SET_RULE`s UNION t INTER s = (s UNION t) INTER s`];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC THEN
SUBGOAL_THEN`{N} INTER bitset (x - 1) = {}`SUBST1_TAC THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN SIMP_TAC[DISJOINT_SING]
THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY] THEN UNDISCH_TAC`bitset c INTER {N} = {N}`
THEN UNDISCH_TAC`bitset d INTER {N} = {N}` THEN ASM_SIMP_TAC[SET_RULE`s UNION t INTER s =
(s UNION t) INTER s`];ALL_TAC] THEN SUBGOAL_THEN `{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD ({N} UNION bitset (c - 2 EXP N) INTER bitset (k - 1)) *
       CARD ({N} UNION bitset (d - 2 EXP N) INTER bitset (k - 1)))} =
 {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD((CARD {N} + CARD (bitset (c - 2 EXP N) INTER bitset (k - 1))) *
       (CARD {N} + CARD (bitset (d - 2 EXP N) INTER bitset (k - 1))))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC THEN
SUBGOAL_THEN`CARD ({N} UNION bitset (c - 2 EXP N) INTER bitset (x - 1))
  = CARD {N} + CARD (bitset (c - 2 EXP N) INTER bitset (x - 1))`SUBST1_TAC
  THENL[MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < c` THEN
SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`CARD ({N} UNION bitset (d - 2 EXP N) INTER bitset (x - 1))
  = CARD {N} + CARD (bitset (d - 2 EXP N) INTER bitset (x - 1))`SUBST1_TAC THENL[MATCH_MP_TAC CARD_UNION
THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`d < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < d` THEN SIMP_TAC[
ARITH_RULE`d - 2 EXP N  < 2 EXP N <=> d < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_SING];ALL_TAC]
THEN SIMP_TAC[CARD_SING] THEN
SIMP_TAC[ARITH_RULE`1 + a = SUC a`;ODD_MULT;ODD;NOT_ODD] THEN RULE_ASSUM_TAC(SIMP_RULE[ODD_MULT]) THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_ODD_CARD) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_CARD_ODD_EQ_EVEN) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] BITAND_ODD_CARD)
THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
SIMP_TAC[GSYM IN_NUMSEG] THEN
ONCE_SIMP_TAC[SET_RULE`{x | x IN s /\ p x /\ q x} = {x | x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`]
THEN SIMP_TAC[NOT_EVEN] THEN
SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x } SUBSET {x |x IN s /\ p x}`;CARD_DIFF]
THEN ASM_SIMP_TAC[GSYM bitand] THEN ONCE_REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`] THEN
ONCE_SIMP_TAC[SET_RULE`{x | x IN s /\ p x /\ q x} = {x | x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`]
THEN SIMP_TAC[NOT_EVEN] THEN
SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x } SUBSET {x |x IN s /\ p x}`;CARD_DIFF]
THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`] THEN
ASM_SIMP_TAC[bitand;IN_NUMSEG] THEN
SUBGOAL_THEN`2 EXP (N - 2) < 2 EXP (N - 1)`ASSUME_TAC THENL[SIMP_TAC[LT_EXP;ARITH]
THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 2 < N - 1`];ALL_TAC] THEN
ASM_SIMP_TAC[ARITH_RULE`2 EXP (N - 2) < 2 EXP (N - 1)
==> 2 EXP (N - 2) + 2 EXP (N - 1) -(2 EXP (N - 1) - 2 EXP (N - 2)) = 2 EXP (N - 2) + 2 EXP (N - 2)`] THEN
SIMP_TAC[GSYM MULT_2] THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 1 = SUC (N - 2)`;EXP];ALL_TAC ] THEN
ASM_SIMP_TAC[] THEN RULE_ASSUM_TAC(SIMP_RULE[NOT_LT]) THEN POP_ASSUM MP_TAC THEN  SIMP_TAC[
ARITH_RULE`d <= 2 EXP N <=> d < 2 EXP N \/ d = 2 EXP N `]
THEN STRIP_TAC THENL[MP_TAC(SPECL[`N:num`;`d:num`] BITAND_ODD_CARD) THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`]
THEN STRIP_TAC THEN SIMP_TAC[ODD_MULT] THEN
SUBGOAL_THEN`{k | (1 <= k /\ (k < 2 EXP N \/ k = 2 EXP N)) /\
      ODD (CARD (bitset c INTER bitset (k - 1) UNION bitset c INTER {N})) /\
     ODD (CARD (bitset d INTER bitset (k - 1) UNION bitset d INTER {N}))} =
  {k | (1 <= k /\ (k < 2 EXP N \/ k = 2 EXP N)) /\
        EVEN (CARD (bitset c INTER bitset (k - 1))) /\
  ODD (CARD (bitset d INTER bitset (k - 1)))}`SUBST1_TAC THENL[SUBGOAL_THEN`bitset c INTER {N} = {N}`SUBST1_TAC
  THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM;INTER] THEN
UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}`
THEN SUBGOAL_THEN`bitset (c - 2 EXP N + 2 EXP N) = bitset c`SUBST1_TAC THENL
[ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`];ALL_TAC]
THEN SET_TAC[IN_UNION];ALL_TAC] THEN SUBGOAL_THEN`bitset d INTER {N} = {}`SUBST1_TAC
THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN MP_TAC(SPECL[`d:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY] THEN
SIMP_TAC[ARITH_RULE`k < 2 EXP N \/ k = 2 EXP N <=> k <= 2 EXP N`] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N ) /\
      ODD (CARD (bitset c INTER bitset (k - 1) UNION {N})) /\
      ODD (CARD (bitset d INTER bitset (k - 1)))}    =
  {k | (1 <= k /\ k <= 2 EXP N) /\
        ODD (CARD (bitset c INTER bitset (k - 1)) + CARD {N}) /\
  ODD (CARD (bitset d INTER bitset (k - 1)))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL [SIMP_TAC[] THEN
STRIP_TAC THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`ASSUME_TAC
THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`(bitset c INTER bitset (x - 1)) INTER {N} = {}`ASSUME_TAC
THENL[ASM_SIMP_TAC[SET_RULE`(s INTER t) INTER u = s INTER (t INTER u)`;INTER_EMPTY];ALL_TAC] THEN
ASM_SIMP_TAC[FINITE_INTER;FINITE_BITSET;GSYM CARD_UNION;FINITE_SING];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC
THEN SUBGOAL_THEN`bitset (x - 1) INTER {N} = {}`ASSUME_TAC THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`] THEN SET_TAC[LT_REFL];ALL_TAC] THEN
SUBGOAL_THEN`(bitset c INTER bitset (x - 1)) INTER {N} = {}`ASSUME_TAC
THENL[ASM_SIMP_TAC[SET_RULE`(s INTER t) INTER u = s INTER (t INTER u)`;INTER_EMPTY];ALL_TAC] THEN
ASM_SIMP_TAC[FINITE_INTER;FINITE_BITSET;CARD_UNION;FINITE_SING];ALL_TAC] THEN
SIMP_TAC[CARD_SING;ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD];ALL_TAC] THEN SIMP_TAC[GSYM NOT_ODD] THEN
SIMP_TAC[ARITH_RULE`k < 2 EXP N \/ k = 2 EXP N <=> k <= 2 EXP N`;GSYM IN_NUMSEG] THEN
SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x} INTER {x |x IN s /\ ~p x /\ q x} = {}`;
GSYM CARD_UNION] THEN SIMP_TAC[SET_RULE`{x |x IN s /\ p x /\ q x } UNION {x |x IN s /\ ~p x /\ q x} =
{x |x IN s /\ q x}`] THEN ASM_SIMP_TAC[GSYM bitand];ALL_TAC] THEN
ASM_SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2] THEN
SIMP_TAC[ARITH_RULE`k < 2 EXP N \/ k = 2 EXP N <=> k <= 2 EXP N`;INTER_IDEMPOT] THEN
SUBGOAL_THEN`CARD
 {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num c INTER bits_of_num (k - 1)) *
       CARD ({N} INTER bits_of_num (k - 1)))} = 0`SUBST1_TAC
       THENL[SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;FINITE_RESTRICT;CARD_EQ_0]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN EQ_TAC
THENL[STRIP_TAC THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x- 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_CLAUSES;MULT_0;ODD];ALL_TAC] THEN SET_TAC[];ALL_TAC]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD(bits_of_num c INTER bits_of_num (k - 1) UNION
          bits_of_num c INTER {N}) * CARD ({N} INTER bits_of_num (k - 1) UNION {N}))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\
        ODD(CARD (bits_of_num c INTER bits_of_num (k - 1) UNION
          bits_of_num c INTER {N}))}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
EQ_TAC THENL[SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC] THEN SIMP_TAC[]
THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC] THEN
SUBGOAL_THEN`bits_of_num c INTER {N} = {N}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM;INTER] THEN
UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}` THEN
SUBGOAL_THEN`bitset (c - 2 EXP N + 2 EXP N) = bitset c`SUBST1_TAC THENL[UNDISCH_TAC`2 EXP N < c`
THEN SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`];ALL_TAC] THEN STRIP_TAC THEN GEN_TAC
THEN ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM;IN_UNION] THEN SET_TAC[];ALL_TAC]
THEN SIMP_TAC[UNION_COMM;INTER_OVER_UNION]
THEN SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
UNDISCH_TAC`bitset (c - 2 EXP N + 2 EXP N) = bitset (c - 2 EXP N) UNION {N}`
THEN ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`] THEN
SIMP_TAC[SET_RULE`(s UNION t) UNION t = s UNION t`]
THEN STRIP_TAC THEN SIMP_TAC[SET_RULE`(s UNION t) INTER (u UNION t) = (s INTER u) UNION t`] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
        ODD (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1) UNION {N}))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\
          ODD (CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)) + CARD {N})}`SUBST1_TAC THENL[
SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC
THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < c` THEN
SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[CARD_SING] THEN SIMP_TAC[ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD]
THEN MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_ODD_CARD) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN
SIMP_TAC[bitand;IN_NUMSEG;ADD_CLAUSES];ALL_TAC]
THEN ASM_SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2;INTER_IDEMPOT] THEN
SUBGOAL_THEN`CARD {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD ({N} INTER bits_of_num (k - 1)) *
       CARD (bits_of_num d INTER bits_of_num (k - 1)))} = 0`SUBST1_TAC
       THENL[SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;FINITE_RESTRICT;CARD_EQ_0]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN EQ_TAC THENL[STRIP_TAC THEN
POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x- 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_CLAUSES;MULT_CLAUSES;ODD];ALL_TAC] THEN SET_TAC[];ALL_TAC]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD ({N} INTER bits_of_num (k - 1) UNION {N}) *
       CARD
       (bits_of_num d INTER bits_of_num (k - 1) UNION
        bits_of_num d INTER {N}))}          =
  {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD  (CARD
       (bits_of_num d INTER bits_of_num (k - 1) UNION
        bits_of_num d INTER {N}))}    `SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
EQ_TAC THENL[SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC]
THEN SIMP_TAC[] THEN STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC] THEN
ASM_CASES_TAC`d < 2 EXP N ` THENL[SUBGOAL_THEN`bits_of_num d INTER {N} = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`d:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN ASM_SIMP_TAC[]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY] THEN
MP_TAC(SPECL[`N:num`;`d:num`] BITAND_ODD_CARD) THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`;
bitand;BITSET_EQ_BITSNUM;IN_NUMSEG;ADD_CLAUSES];ALL_TAC]
THEN POP_ASSUM MP_TAC THEN SIMP_TAC[ARITH_RULE`~(d < 2 EXP N) <=> 2 EXP N <= d`] THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[ARITH_RULE`2 EXP N <= d <=> d =  2 EXP N \/ 2 EXP N < d`]
THEN STRIP_TAC THENL[UNDISCH_TAC`d = 2 EXP N` THEN ASM_ARITH_TAC;ALL_TAC] THEN
UNDISCH_TAC`bitset (d - 2 EXP N + 2 EXP N) = bitset (d - 2 EXP N) UNION {N}` THEN
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < d ==> d - 2 EXP N + 2 EXP N = d`] THEN SIMP_TAC[BITSET_EQ_BITSNUM]
THEN SIMP_TAC[SET_RULE`(s UNION t) INTER t = s INTER t UNION t`] THEN
SIMP_TAC[ SET_RULE`s INTER t UNION t = t`]
THEN SIMP_TAC[SET_RULE`(s UNION t) INTER  u = s INTER u UNION t INTER u`] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
ODD(CARD((bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1) UNION
    {N} INTER bits_of_num (k - 1)) UNION {N}))} = {k | (1 <= k /\ k <= 2 EXP N) /\
ODD(CARD ((bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1)) UNION {N} ))}`SUBST1_TAC THENL[
SIMP_TAC[IN_ELIM_THM;EXTENSION] THEN GEN_TAC THEN EQ_TAC THENL[STRIP_TAC THEN ASM_SIMP_TAC[]
THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC
THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC THENL[
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`] THEN SET_TAC[LT_REFL];ALL_TAC] THEN
ASM_SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN STRIP_TAC THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1) UNION {N}))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\ ODD  (CARD (bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1))
  + CARD {N})}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITS_OF_NUM;FINITE_INTER;FINITE_SING]
THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`d < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < d` THEN
SIMP_TAC[ARITH_RULE`d - 2 EXP N  < 2 EXP N <=> d < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[CARD_SING;ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD;GSYM IN_NUMSEG] THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] BITAND_ODD_CARD)
THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN
SIMP_TAC[bitand;BITSET_EQ_BITSNUM;ADD_CLAUSES];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`2 EXP N <= d <=> d = 2 EXP N \/ 2 EXP N < d`]) THEN POP_ASSUM MP_TAC
THEN STRIP_TAC THENL
[ASM_SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2;INTER_IDEMPOT] THEN
SIMP_TAC[SET_RULE`s INTER t UNION s = s`;CARD_SING;MULT_CLAUSES] THEN
SUBGOAL_THEN`CARD {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
          (CARD (bits_of_num c INTER bits_of_num (k - 1)) *
         CARD ({N} INTER bits_of_num (k - 1)))} = 0`SUBST1_TAC
THENL[SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;FINITE_RESTRICT;CARD_EQ_0]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN EQ_TAC
THENL[STRIP_TAC THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x- 1) = {}`SUBST1_TAC THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_CLAUSES;MULT_0;ODD];ALL_TAC]
THEN SET_TAC[];ALL_TAC] THEN ASM_CASES_TAC`2 EXP N < c`
THENL[MP_TAC(SPECL[`c - 2 EXP N`;`N:num`]BITSET_ADD) THEN
ASM_SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2]) THEN
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`] THEN STRIP_TAC THEN
ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM;IN_UNION] THEN SIMP_TAC[SET_RULE`(s UNION t) INTER t = t`]
THEN SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD ((bitset (c - 2 EXP N) INTER bitset (k - 1) UNION
{N} INTER bitset (k - 1)) UNION {N}))} = {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset (c - 2 EXP N) INTER bitset (k - 1) UNION {N}))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[SIMP_TAC[] THEN
STRIP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC]
THEN SIMP_TAC[BITSET_EQ_BITSNUM]
THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC]
THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN STRIP_TAC THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN ASM_SIMP_TAC[UNION_EMPTY;CARD_SING;MULT_CLAUSES];ALL_TAC]
THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num (c - 2 EXP N) INTER bits_of_num (k - 1) UNION {N}))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\ ODD  (CARD (bits_of_num (c - 2 EXP N) INTER bits_of_num (k - 1))
  + CARD {N})}`SUBST1_TAC THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION THEN
SIMP_TAC[FINITE_BITS_OF_NUM;FINITE_INTER;FINITE_SING] THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`c < 2 EXP N + 2 EXP N` THEN UNDISCH_TAC`2 EXP N < c` THEN
SIMP_TAC[ARITH_RULE`c < 2 EXP N + 2 EXP N <=> c - 2 EXP N  < 2 EXP N`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN
SIMP_TAC[CARD_SING] THEN SIMP_TAC[ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD;GSYM IN_NUMSEG]
THEN MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_ODD_CARD) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`;ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
THEN ASM_SIMP_TAC[bitand;ARITH_RULE`0 < N <=> 1 < 1 + N`;ADD] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN ASM_SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`;
ARITH_RULE`0 < N <=> 1 < 1 + N`;bitand;GSYM BITSET_EQ_BITSNUM];ALL_TAC]
THEN RULE_ASSUM_TAC(SIMP_RULE[NOT_LT;LE_LT]) THEN POP_ASSUM MP_TAC THEN
MP_TAC(ARITH_RULE`~(c = d:num) /\ d = 2 EXP N ==> ~(c = 2 EXP N)`)
THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN
SUBGOAL_THEN`bitset c INTER {N} = {}`SUBST1_TAC THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN
MP_TAC(SPECL[`c:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN ASM_SIMP_TAC[] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY;GSYM bitand;ADD;GSYM IN_NUMSEG]
THEN MP_TAC(SPECL[`N:num`;`c:num`] BITAND_ODD_CARD) THEN ASM_SIMP_TAC[ARITH_RULE`0 < N <=> 1 < SUC N`];ALL_TAC]
THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] BITSET_ADD) THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD]
THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`] THEN SUBGOAL_THEN`bitset (d - 2 EXP N + 2 EXP N) = bitset d`SUBST1_TAC
THENL[ASM_SIMP_TAC[ARITH_RULE`2 EXP N < d ==> d - 2 EXP N + 2 EXP N = d`];ALL_TAC]
THEN STRIP_TAC THEN SUBGOAL_THEN`bitset d INTER {N} = {N}`SUBST1_TAC THENL[SIMP_TAC[INTER;IN_ELIM_THM;EXTENSION]
THEN ASM_SIMP_TAC[IN_UNION] THEN SET_TAC[];ALL_TAC] THEN ASM_CASES_TAC`c < 2 EXP N`
THENL[SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`bits_of_num c INTER {N} = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`c:num`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN
ASM_SIMP_TAC[] THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY] THEN ASM_SIMP_TAC[]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD (bits_of_num c INTER bits_of_num (k - 1)) *
       CARD (bits_of_num d INTER bits_of_num (k - 1)))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD (bits_of_num c INTER bits_of_num (k - 1)) *
       CARD (bitset (d - 2 EXP N) INTER bits_of_num (k - 1)))}`SUBST1_TAC
       THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC
THENL[SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN ASM_SIMP_TAC[] THEN
SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bitset (x- 1) = {}`SUBST1_TAC
THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN
SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN
SUBGOAL_THEN`{N} INTER bitset (x- 1) = {}`SUBST1_TAC THENL[ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2)
THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN SIMP_TAC[DISJOINT_SING] THEN
MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`x <= 2 EXP N` THEN UNDISCH_TAC`1 <= x` THEN
SIMP_TAC[ARITH_RULE`1 <= x ==> x <= 2 EXP N ==> x - 1  < 2 EXP N`] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN
ASM_SIMP_TAC[GSYM BITSET_EQ_BITSNUM] THEN
SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`] THEN
SIMP_TAC[SET_RULE`(s UNION t) UNION u = s UNION t UNION u`;SET_RULE`s INTER u UNION s = s`] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset c INTER bitset (k - 1)) *
       CARD (bitset (d - 2 EXP N) INTER bitset (k - 1) UNION {N}))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset c INTER bitset (k - 1)) *
       (CARD (bitset (d - 2 EXP N) INTER bitset (k - 1)) + CARD{N}))}`SUBST1_TAC
THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN REPEAT AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION
THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT]
THEN SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2]) THEN
UNDISCH_TAC`d < 2 EXP N + 2 EXP N` THEN UNDISCH_TAC`2 EXP N < d` THEN
SIMP_TAC[ARITH_RULE`c < 2 EXP N + 2 EXP N <=> c - 2 EXP N  < 2 EXP N`] THEN SET_TAC[LT_REFL];ALL_TAC]
THEN SIMP_TAC[CARD_SING;ODD_MULT;ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD;GSYM IN_NUMSEG]
THEN MP_TAC(SPECL[`N:num`;`c:num`] BITAND_ODD_CARD) THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`] THEN
SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;SET_RULE`{x |x IN s /\ p x /\ q x} INTER {x |x IN s /\ p x /\ ~q x} = {}`;
GSYM CARD_UNION;GSYM NOT_ODD] THEN SIMP_TAC[SET_RULE`{x |x IN s /\ p x /\ q x} UNION
{x |x IN s /\ p x /\ ~q x} = {x |x IN s /\ p x}`;bitand];ALL_TAC] THEN RULE_ASSUM_TAC(SIMP_RULE[
ARITH_RULE`~(c < 2 EXP N) <=> c = 2 EXP N \/ 2 EXP N < c `]) THEN POP_ASSUM MP_TAC THEN
STRIP_TAC THENL[ASM_SIMP_TAC[BITSET_EQ_BITSNUM;BITS_OF_NUM_POW2;INTER_IDEMPOT] THEN
SIMP_TAC[SET_RULE`s INTER u UNION s = s`;SET_RULE`(s UNION {N}) INTER u UNION {N} = s INTER u UNION {N}`;
CARD_SING;MULT_CLAUSES] THEN SUBGOAL_THEN`CARD
 {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (CARD ({N} INTER bits_of_num (k - 1)) *
       CARD ((bits_of_num (d - 2 EXP N) UNION {N}) INTER bits_of_num (k - 1)))} = 0`SUBST1_TAC
       THENL[SIMP_TAC[GSYM IN_NUMSEG;FINITE_NUMSEG;FINITE_RESTRICT;CARD_EQ_0]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN SIMP_TAC[IN_NUMSEG] THEN
EQ_TAC THENL[STRIP_TAC THEN POP_ASSUM MP_TAC THEN SUBGOAL_THEN`{N} INTER bits_of_num (x- 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_CLAUSES;MULT_CLAUSES;ODD];ALL_TAC] THEN SET_TAC[];ALL_TAC]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1) UNION {N}))} =
      {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bits_of_num (d - 2 EXP N) INTER bits_of_num (k - 1)) + CARD {N})}`SUBST1_TAC
      THENL[RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2]) THEN
SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITS_OF_NUM;FINITE_INTER;FINITE_SING]
THEN ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN UNDISCH_TAC`d < 2 EXP N + 2 EXP N` THEN UNDISCH_TAC`2 EXP N < d` THEN
SIMP_TAC[ARITH_RULE`c < 2 EXP N + 2 EXP N <=> c - 2 EXP N  < 2 EXP N`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_SING;ARITH_RULE`N + 1 = SUC N`;ODD;NOT_ODD;
GSYM IN_NUMSEG;GSYM BITSET_EQ_BITSNUM;GSYM bitand] THEN
 MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] BITAND_ODD_CARD) THEN
 SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`;ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
 THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`]
THEN SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`;ADD];ALL_TAC] THEN
MP_TAC (SPECL[`c - 2 EXP N`;`N:num`] BITSET_ADD) THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD]
THEN ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`] THEN
ASM_SIMP_TAC[ARITH_RULE`2 EXP N < c ==> c - 2 EXP N + 2 EXP N = c`] THEN STRIP_TAC
THEN SIMP_TAC[SET_RULE`(s UNION t) INTER t = t`]
THEN SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD
      (  CARD ((bitset (c - 2 EXP N) UNION {N}) INTER bitset (k - 1)) *
         CARD ((bitset (d - 2 EXP N) UNION {N}) INTER bitset (k - 1)))} =
  {k | (1 <= k /\ k <= 2 EXP N) /\
        ODD(CARD(bitset (c - 2 EXP N) INTER bitset (k - 1)) *
  CARD(bitset (d - 2 EXP N) INTER bitset (k - 1)))}`SUBST1_TAC THENL[
  SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN EQ_TAC THENL[SIMP_TAC[]
THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN SIMP_TAC[]
THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN
SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD ((bitset (c - 2 EXP N) UNION {N}) INTER bitset (k - 1) UNION {N}) *
       CARD ((bitset (d - 2 EXP N) UNION {N}) INTER bitset (k - 1) UNION {N}))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset (c - 2 EXP N) INTER bitset (k - 1) UNION {N}) *
       CARD (bitset (d - 2 EXP N) INTER bitset (k - 1) UNION {N}))}`SUBST1_TAC
       THENL[SIMP_TAC[SET_RULE`(s UNION t) INTER u = s INTER u UNION t INTER u`]
       THEN SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC
THEN EQ_TAC THENL[SIMP_TAC[] THEN STRIP_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[BITSET_EQ_BITSNUM]
THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN SIMP_TAC[] THEN STRIP_TAC THEN
POP_ASSUM MP_TAC THEN SIMP_TAC[BITSET_EQ_BITSNUM] THEN SUBGOAL_THEN`{N} INTER bits_of_num (x - 1) = {}`SUBST1_TAC
THENL[MP_TAC(SPECL[`x-1`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ))
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= x ==> x <= a ==> x - 1 < a`]
THEN SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[UNION_EMPTY];ALL_TAC] THEN
SUBGOAL_THEN`{k | (1 <= k /\ k <= 2 EXP N) /\
      ODD(CARD (bitset (c - 2 EXP N) INTER bitset (k - 1) UNION {N}) *
       CARD (bitset (d - 2 EXP N) INTER bitset (k - 1) UNION {N}))} =
       {k | (1 <= k /\ k <= 2 EXP N) /\
      ODD((CARD (bitset (c - 2 EXP N) INTER bitset (k - 1)) + CARD {N}) *
      (CARD (bitset (d - 2 EXP N) INTER bitset (k - 1)) + CARD {N}))}`SUBST1_TAC
      THENL[SIMP_TAC[EXTENSION;IN_ELIM_THM] THEN GEN_TAC THEN
REPEAT AP_TERM_TAC THEN SUBGOAL_THEN`CARD (bitset (c - 2 EXP N) INTER bitset (x - 1) UNION {N})
  = CARD (bitset (c - 2 EXP N) INTER bitset (x - 1)) + CARD {N}`SUBST1_TAC
  THENL[MATCH_MP_TAC CARD_UNION THEN SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`c - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN
UNDISCH_TAC`c < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < c` THEN
SIMP_TAC[ARITH_RULE`c - 2 EXP N  < 2 EXP N <=> c < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SUBGOAL_THEN`CARD (bitset (d - 2 EXP N) INTER bitset (x - 1) UNION {N})
  = CARD (bitset (d - 2 EXP N) INTER bitset (x - 1)) + CARD {N}`SUBST1_TAC THENL[MATCH_MP_TAC CARD_UNION THEN
  SIMP_TAC[FINITE_BITSET;FINITE_INTER;FINITE_SING] THEN
ASSUME_TAC(SPEC`N:num` BITS_OF_NUM_POW2) THEN SIMP_TAC[BITSET_EQ_BITSNUM;GSYM DISJOINT] THEN
SIMP_TAC[DISJOINT_SING] THEN MP_TAC(SPECL[`d - 2 EXP N`;`N:num`] (GSYM BITS_OF_NUM_SUBSET_NUMSEG_EQ)) THEN
UNDISCH_TAC`d < 2 EXP SUC N` THEN UNDISCH_TAC`2 EXP N < d` THEN
SIMP_TAC[ARITH_RULE`d - 2 EXP N  < 2 EXP N <=> d < 2 EXP N + 2 EXP N`]
THEN SIMP_TAC[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2] THEN
SET_TAC[LT_REFL];ALL_TAC] THEN SIMP_TAC[CARD_SING];ALL_TAC] THEN
SIMP_TAC[CARD_SING;ARITH_RULE`a + 1 = SUC a`;ODD_MULT;ODD] THEN RULE_ASSUM_TAC(SIMP_RULE[ODD_MULT]) THEN
MP_TAC(SPECL[`N:num`;`d - 2 EXP N`] BITAND_ODD_CARD) THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] BITAND_ODD_CARD) THEN
SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN REPEAT STRIP_TAC THEN
MP_TAC(SPECL[`N:num`;`c - 2 EXP N`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`] THEN
SIMP_TAC[ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`] THEN
SIMP_TAC[GSYM MULT_2;ARITH_RULE`2 * 2 EXP N = 2 EXP 1 * 2 EXP N `;GSYM EXP_ADD] THEN
ASM_SIMP_TAC[ARITH_RULE`1 + N = SUC N`;ARITH_RULE`1 < N ==> 0 < N`] THEN STRIP_TAC THEN
FIRST_X_ASSUM(MP_TAC o SPECL[`c - 2 EXP N `;`d - 2 EXP N`]) THEN
RULE_ASSUM_TAC(SIMP_RULE[ARITH_RULE`SUC N = 1 + N`;EXP_ADD;EXP_1;MULT_2])
THEN ASM_SIMP_TAC[ARITH_RULE`0 < c - a <=> a < c`;ARITH_RULE`n - 2 EXP N  < 2 EXP N  <=> n < 2 EXP N + 2 EXP N`;
ARITH_RULE`2 EXP N < c /\ 2 EXP N < d /\ ~(c = d) ==> ~(c - 2 EXP N = d - 2 EXP N)`;bitand]
THEN STRIP_TAC THEN SIMP_TAC[NOT_ODD;GSYM IN_NUMSEG] THEN
ONCE_SIMP_TAC[SET_RULE`{x | x IN s /\ p x /\ q x} = {x | x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`]
THEN SIMP_TAC[NOT_EVEN] THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;
SET_RULE`{x |x IN s /\ p x /\ q x } SUBSET {x |x IN s /\ p x}`;CARD_DIFF]
THEN ASM_SIMP_TAC[GSYM bitand] THEN ONCE_REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`] THEN
ONCE_SIMP_TAC[SET_RULE`{x | x IN s /\ p x /\ q x} = {x | x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`]
THEN SIMP_TAC[NOT_EVEN] THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;
SET_RULE`{x |x IN s /\ p x /\ q x } SUBSET {x |x IN s /\ p x}`;CARD_DIFF]
THEN ONCE_REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`] THEN ASM_SIMP_TAC[bitand;IN_NUMSEG]
THEN SUBGOAL_THEN`2 EXP (N - 2) < 2 EXP (N - 1)`ASSUME_TAC THENL[SIMP_TAC[LT_EXP;ARITH] THEN
ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 2 < N - 1`];ALL_TAC] THEN
ASM_SIMP_TAC[ARITH_RULE`2 EXP (N - 2) < 2 EXP (N - 1) ==>
2 EXP (N - 2) + 2 EXP (N - 1) -(2 EXP (N - 1) - 2 EXP (N - 2)) = 2 EXP (N - 2) + 2 EXP (N - 2)`]
THEN SIMP_TAC[GSYM MULT_2] THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 1 = SUC (N - 2)`;EXP]
);;

let BITAND_ODD_EVEN_CARD = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ EVEN(CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`,
REPEAT STRIP_TAC THEN MP_TAC (SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_ODD_CARD) THEN ASM_SIMP_TAC[]
THEN MP_TAC (SPECL[`N:num`;`c:num`] BITAND_ODD_CARD) THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`] THEN REPEAT STRIP_TAC THEN
ONCE_REWRITE_TAC[SET_RULE`{x |x IN s /\ p x /\ q x} = {x |x IN s /\ p x} DIFF {x |x IN s /\ p x /\ ~q x}`] THEN
ASM_SIMP_TAC[NOT_EVEN;FINITE_NUMSEG;FINITE_RESTRICT;CARD_DIFF;SET_RULE`{x |x IN s /\ p x /\ q x} SUBSET {x |x IN s /\ p x}`]
THEN SIMP_TAC[ARITH_RULE`a - b = b:num <=> a = b + b`] THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 1 = SUC (N - 2)`;EXP;MULT_2] );;

let BITAND_EVEN_EVEN_CARD = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       EVEN(CARD (bitand c (k - 1))) /\ EVEN(CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`,
REPEAT STRIP_TAC THEN MP_TAC (SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_EVEN_CARD) THEN ASM_SIMP_TAC[]
THEN STRIP_TAC THEN ONCE_REWRITE_TAC[SET_RULE`{x |x IN s /\ p x /\ q x} = {x |x IN s /\ q x} DIFF {x |x IN s /\ ~p x /\ q x}`]
THEN ASM_SIMP_TAC[NOT_EVEN;FINITE_NUMSEG;FINITE_RESTRICT;CARD_DIFF;SET_RULE`{x |x IN s /\ p x /\ q x} SUBSET {x |x IN s /\ q x}`]
THEN MP_TAC(SPECL[`N:num`;`d:num`] (GSYM BITAND_CARD_ODD_EQ_EVEN)) THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`] THEN
MP_TAC (SPECL[`N:num`;`d:num`] BITAND_ODD_CARD) THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> 0 < N`] THEN
SIMP_TAC[ARITH_RULE`a - b = b:num <=> a = b + b`] THEN ASM_SIMP_TAC[ARITH_RULE`1 < N ==> N - 1 = SUC (N - 2)`;EXP;MULT_2]);;

let BITAND_EVEN_ODD_CARD = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       EVEN(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))} = 2 EXP (N - 2)`,
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`N:num`;`d:num`;`c:num`] BITAND_ODD_EVEN_CARD) THEN
ASM_SIMP_TAC[] THEN REWRITE_TAC[TAUT`P /\ Q /\ R <=> P /\ R /\ Q`]);;

let BITAND_CARD_EVEN2_EQ_ODD2 = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       EVEN(CARD (bitand c (k - 1))) /\ EVEN(CARD (bitand d (k - 1)))} = CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))}`,
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_EVEN_EVEN_CARD) THEN
MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_ODD_CARD) THEN ASM_SIMP_TAC[]);;

let BITAND_CARD_EVEN_ODD_EQ_ODD2 = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       EVEN(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))} = CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))}`,
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_EVEN_ODD_CARD) THEN
MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_ODD_CARD) THEN ASM_SIMP_TAC[]);;

let BITAND_CARD_ODD_EVEN_EQ_ODD2 = prove
(`!N c d:num.
  0 < d /\ d < 2 EXP N /\ 0 < c /\ c < 2 EXP N /\ 1 < N /\ ~(c = d) ==> CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ EVEN(CARD (bitand d (k - 1)))} = CARD {k | k IN 1..2 EXP N /\
       ODD(CARD (bitand c (k - 1))) /\ ODD(CARD (bitand d (k - 1)))}`,
REPEAT STRIP_TAC THEN MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_EVEN_CARD) THEN
MP_TAC(SPECL[`N:num`;`c:num`;`d:num`] BITAND_ODD_ODD_CARD) THEN ASM_SIMP_TAC[]);;

let hadamard_n = new_definition
  `hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow = lambda i j.
     if EVEN (CARD(bitand (i-1)(j-1)))
     then Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))
     else --Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))`;;

(* ------------------------------------------------------------------------- *)
(* Definition of n-fold tensor product of 2-dimensional matrices.            *)
(* ------------------------------------------------------------------------- *)

let tensor_n2 = new_definition
`!m:(complex^(2,1)finite_pow^(2,1)finite_pow)list.
  tensor_n2 m =
    lambda i j. cproduct (0..LENGTH m - 1)
      (\k. EL k (REVERSE m) $(((i-1) DIV (2 EXP k)) MOD 2 + 1)
                   $(((j-1) DIV (2 EXP k)) MOD 2 + 1))`;;

(* ----------------------------------------------------------------------------- *)
(* cmatrix_list: Generates a list of n 2D matrices by applying function f to each index k ∈ {0,...,n-1}.
 Parameter f supports:
  - Constant gates:  \k. Hadamard       (n Hadamard gates)
  - Conditional gates: \k. if k = 0 then X else Z
  - CNOT control:   \k. if k = c then CNOT_c_t else I  (c: control, t: target)   *)
(* ----------------------------------------------------------------------------- *)

let cmatrix_list = new_definition
`!n:num f:num -> complex^(2,1)finite_pow^(2,1)finite_pow.
  (cmatrix_list f n):(complex^(2,1)finite_pow^(2,1)finite_pow)list = MAP f (list_of_seq (\k. k) n)`;;

let n_hadamard = new_definition
`n_hadamard (n:num) =
 tensor_n2 (cmatrix_list (\k. hadamard) n)`;;

let N_HADAMARD_EQHADAMARD_N = prove
(`n_hadamard (dimindex(:N)) = hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow`,
  SIMP_TAC[n_hadamard;hadamard_n;cmatrix_list;tensor_n2] THEN
  SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[LENGTH_MAP;LENGTH_LIST_OF_SEQ] THEN
  SUBGOAL_THEN`MAP (\k. hadamard) (list_of_seq (\k. k) (dimindex (:N)))
    = REPLICATE (LENGTH (list_of_seq (\k. k) (dimindex (:N)))) hadamard`SUBST1_TAC
    THENL[SPEC_TAC(`list_of_seq (\k. k) (dimindex (:N))`,`l:num list`)
    THEN LIST_INDUCT_TAC THENL[SIMP_TAC[MAP;REPLICATE;LENGTH];ALL_TAC] THEN
    ASM_SIMP_TAC[REPLICATE;LENGTH;MAP];ALL_TAC] THEN
  SIMP_TAC[LENGTH_LIST_OF_SEQ] THEN SIMP_TAC[REVERSE_REPLICATE] THEN
  SUBGOAL_THEN`cproduct (0..dimindex (:N) - 1)
  (\k. EL k (REPLICATE (dimindex (:N)) hadamard)$
      (((i - 1) DIV 2 EXP k) MOD 2 + 1)$
      (((i' - 1) DIV 2 EXP k) MOD 2 + 1)) =
      cproduct (0..dimindex (:N) - 1)
  (\k. hadamard$
      (((i - 1) DIV 2 EXP k) MOD 2 + 1)$
      (((i' - 1) DIV 2 EXP k) MOD 2 + 1))`SUBST1_TAC THENL[MATCH_MP_TAC CPRODUCT_EQ
      THEN SIMP_TAC[IN_NUMSEG] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC
      THEN AP_THM_TAC THEN AP_TERM_TAC THEN MATCH_MP_TAC EL_REPLICATE THEN
      ASM_SIMP_TAC[ARITH_RULE`1 <= b /\ a <= b - 1 ==> a < b`;DIMINDEX_GE_1];ALL_TAC]
      THEN SIMP_TAC[MOD_2_CASES] THEN SIMP_TAC[GSYM NOT_ODD;COND_SWAP] THEN
      SIMP_TAC[COND_RAND] THEN SIMP_TAC[COND_RATOR;ARITH_RULE`1+1=2`;ADD] THEN
      SIMP_TAC[GSYM IN_BITS_OF_NUM] THEN SIMP_TAC[bitand;bitset;BITSET_EQ_BITSNUM] THEN
  SUBGOAL_THEN`(\k. hadamard$
           (if k IN bits_of_num (i - 1) then 2 else 1)$
           (if k IN bits_of_num (i' - 1) then 2 else 1)) =
           (\k.if k IN bits_of_num (i - 1) /\ k IN bits_of_num (i' - 1)
           then  --Cx(&1 / sqrt(&2))
           else Cx(&1 / sqrt(&2)))`SUBST1_TAC THENL[SIMP_TAC[FUN_EQ_THM] THEN GEN_TAC THEN
           COND_CASES_TAC THEN COND_CASES_TAC THEN SIMP_TAC[HADAMARD_EQ;LAMBDA_BETA;
           DIMINDEX_2;ARITH_RULE`1 <= 2 /\ 2 <= 2`;DIMINDEX_FINITE_POW;DIMINDEX_1;EXP_1;
           ARITH;ARITH_RULE`1 <= 1 /\ 1 <= 2`];ALL_TAC] THEN
           SIMP_TAC[GSYM IN_INTER] THEN
  SUBGOAL_THEN`(0..dimindex (:N) - 1) = (bits_of_num (i - 1) INTER bits_of_num (i' - 1)) UNION
  ((0..dimindex (:N) - 1) DIFF (bits_of_num (i - 1) INTER bits_of_num (i' - 1)))`SUBST1_TAC
  THENL[MATCH_MP_TAC UNION_DIFF THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC` bits_of_num (i - 1) ` THEN SIMP_TAC[INTER_SUBSET] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC`{k | k < dimindex(:N)}` THEN
  SIMP_TAC[BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN ASM_SIMP_TAC[GSYM DIMINDEX_FINITE_POW;GSYM DIMINDEX_2;
  SUBSET;IN_ELIM_THM;IN_NUMSEG;ARITH] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN`cproduct (bits_of_num (i - 1) INTER bits_of_num (i' - 1) UNION
  (0..dimindex (:N) - 1) DIFF bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      (\k. if k IN bits_of_num (i - 1) INTER bits_of_num (i' - 1)
           then --Cx (&1 / sqrt (&2))
           else Cx (&1 / sqrt (&2))) = cproduct (bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      (\k. if k IN bits_of_num (i - 1) INTER bits_of_num (i' - 1)
           then --Cx (&1 / sqrt (&2))
           else Cx (&1 / sqrt (&2))) * cproduct ((0..dimindex (:N) - 1) DIFF
       bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      (\k. if k IN bits_of_num (i - 1) INTER bits_of_num (i' - 1)
           then --Cx (&1 / sqrt (&2))
           else Cx (&1 / sqrt (&2)))`SUBST1_TAC THENL[MATCH_MP_TAC CPRODUCT_UNION
    THEN SIMP_TAC[FINITE_BITS_OF_NUM;FINITE_INTER;FINITE_DIFF;FINITE_NUMSEG] THEN
    SIMP_TAC[SET_RULE`DISJOINT s (t DIFF s)`];ALL_TAC] THEN
    SIMP_TAC[CPRODUCT_CONST;FINITE_INTER;FINITE_BITS_OF_NUM] THEN SIMP_TAC[DIFF] THEN
    SIMP_TAC[CPRODUCT_CONST;FINITE_INTER;FINITE_BITS_OF_NUM;FINITE_DIFF;GSYM DIFF;FINITE_NUMSEG] THEN
    COND_CASES_TAC THENL[ASM_SIMP_TAC[COMPLEX_POW_NEG;GSYM NOT_ODD] THEN
    SIMP_TAC[COMPLEX_MUL_LNEG;GSYM COMPLEX_POW_ADD] THEN
      SUBGOAL_THEN`CARD (bits_of_num (i - 1) INTER bits_of_num (i' - 1)) +
      CARD((0..dimindex (:N) - 1) DIFF bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      = CARD(0 .. dimindex(:N) - 1)`SUBST1_TAC THENL[MATCH_MP_TAC CARD_UNION_EQ THEN
      SIMP_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC (SET_RULE`s SUBSET t ==> s INTER (t DIFF s)
      = {} /\ s UNION (t DIFF s) = t`) THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC` bits_of_num (i - 1) ` THEN SIMP_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC`{k | k < dimindex(:N)}` THEN
    SIMP_TAC[BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN ASM_SIMP_TAC[GSYM DIMINDEX_FINITE_POW;
    GSYM DIMINDEX_2;SUBSET;IN_ELIM_THM;IN_NUMSEG;ARITH] THEN ASM_ARITH_TAC;ALL_TAC] THEN
  SIMP_TAC[CARD_NUMSEG;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_CLAUSES] THEN
  SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= a ==> (a - 1 + 1) - 0 = a`] THEN
  AP_TERM_TAC THEN SIMP_TAC[GSYM CX_POW] THEN AP_TERM_TAC THEN SIMP_TAC[REAL_POW_DIV;
  REAL_POW_ONE] THEN AP_TERM_TAC THEN SIMP_TAC[SQRT_POW];ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM NOT_ODD;COMPLEX_POW_NEG] THEN SIMP_TAC[GSYM COMPLEX_POW_ADD] THEN
  SUBGOAL_THEN`CARD (bits_of_num (i - 1) INTER bits_of_num (i' - 1)) +
      CARD((0..dimindex (:N) - 1) DIFF bits_of_num (i - 1) INTER bits_of_num (i' - 1))
      = CARD(0 .. dimindex(:N) - 1)`SUBST1_TAC THENL[MATCH_MP_TAC CARD_UNION_EQ THEN
      SIMP_TAC[FINITE_NUMSEG] THEN MATCH_MP_TAC (SET_RULE`s SUBSET t ==> s INTER (t DIFF s)
      = {} /\ s UNION (t DIFF s) = t`) THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC` bits_of_num (i - 1) ` THEN SIMP_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC`{k | k < dimindex(:N)}` THEN
    SIMP_TAC[BITS_OF_NUM_SUBSET_NUMSEG_EQ] THEN ASM_SIMP_TAC[GSYM DIMINDEX_FINITE_POW;
    GSYM DIMINDEX_2;SUBSET;IN_ELIM_THM;IN_NUMSEG;ARITH] THEN ASM_ARITH_TAC;ALL_TAC] THEN
    SIMP_TAC[CARD_NUMSEG;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_CLAUSES] THEN
  SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= a ==> (a - 1 + 1) - 0 = a`] THEN
  SIMP_TAC[GSYM CX_POW;REAL_POW_DIV;REAL_POW_ONE] THEN REPEAT AP_TERM_TAC THEN
  SIMP_TAC[SQRT_POW]
);;

let NHADAMARD_MAT = prove
 (`!i j.
        1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
        1 <= j /\ j <= dimindex(:(2,N)finite_pow)
        ==> (hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow)$i$j = if EVEN (CARD(bitand (i-1)(j-1)))
        then Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))
                   else --Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))`,
  REPEAT GEN_TAC THEN CHOOSE_TAC (SPEC_ALL FINITE_INDEX_INRANGE)
  THEN ASM_SIMP_TAC[hadamard_n;LAMBDA_BETA]);;

let NHADAMARD_HERMITIAN = prove
(` hermitian_matrix hadamard_n = hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow `,
SIMP_TAC[hermitian_matrix;hadamard_n] THEN
 SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
SIMP_TAC[COND_CNJ;GSYM CX_NEG;CNJ_CX;BITAND_SYM]);;

let NHADAMARD_UNITARY = prove
(`unitary_matrix (hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[unitary_matrix;cmatrix_mul;id_cmatrix] THEN
SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN SIMP_TAC[hermitian_matrix;LAMBDA_BETA;NHADAMARD_MAT]
THEN SIMP_TAC[COND_CNJ;CNJ_NEG;CNJ_CX;COND_LMUL;COND_RMUL] THEN
SIMP_TAC[GSYM CX_MUL;COMPLEX_MUL_RNEG;COMPLEX_MUL_LNEG;COMPLEX_NEG_MUL2]
THEN SIMP_TAC[GSYM REAL_POW_2;DIMINDEX_GE_1;ONE_DIV_SQRTN] THEN
REPEAT STRIP_TAC THENL [ASM_CASES_TAC`i = i':num` THENL [ASM_SIMP_TAC[]
THEN SIMP_TAC[COND_ID;VSUM_CONST_NUMSEG;ARITH_RULE`(a+1)-1 = a`;COMPLEX_CMUL;GSYM CX_MUL]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
SIMP_TAC[REAL_ARITH`a * &1 / a  =a / a`;GSYM REAL_OF_NUM_POW;POW_REFL]
;ALL_TAC] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[FINITE_NUMSEG;VSUM_CASES;NOT_EVEN]
THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;VSUM_CASES;VSUM_CONST] THEN
SIMP_TAC[SET_RULE`{k | k IN {k | k IN t /\ P k} /\ Q k} = {k | k IN t /\  P k /\ Q k}`]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[NOT_EVEN] THEN
SIMP_TAC[COMPLEX_CMUL;GSYM CX_MUL;GSYM CX_ADD;GSYM CX_SUB;GSYM CX_NEG] THEN
AP_TERM_TAC THEN SIMP_TAC[REAL_ARITH`a * b + c * --b = b * (a - c:real)`] THEN
SIMP_TAC[REAL_ARITH`a * --b + c * b = b * (c - a:real)`] THEN
SIMP_TAC[REAL_ARITH`a * b + a * c = a * (b + c:real)`;REAL_ENTIRE] THEN
SUBGOAL_THEN`~(&1 / &(2 EXP dimindex (:N)) = &0)`ASSUME_TAC THENL
[MATCH_MP_TAC REAL_LT_IMP_NZ THEN SIMP_TAC[real_div;REAL_ARITH`&0 < &1 * a <=> &0 < a`]
THEN MATCH_MP_TAC REAL_LT_INV THEN SIMP_TAC[REAL_OF_NUM_LT;SPECL[`dimindex(:N)`;`2`] EXP_LT_0]
THEN ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[BITAND_SYM] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i' - 1`;`i - 1`]BITAND_CARD_EVEN2_EQ_ODD2) THEN
MP_TAC(SPECL[`dimindex(:N)`;`i' - 1`;`i - 1`]BITAND_CARD_EVEN_ODD_EQ_ODD2)
THEN MP_TAC(SPECL[`dimindex(:N)`;`i' - 1`;`i - 1`]BITAND_CARD_ODD_EVEN_EQ_ODD2) THEN
RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_FINITE_POW;DIMINDEX_2])
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`] THEN
ASM_SIMP_TAC[ ARITH_RULE`1 <= a /\ 1 <= b /\  ~(a = b) ==> ~(a - 1 = b - 1)`]
THEN ASM_CASES_TAC`i = 1` THENL[ASM_SIMP_TAC[ARITH;BITAND_0;EVEN;ODD;SET_RULE`{x |F} = {}`;CARD_CLAUSES]
THEN MP_TAC(SPECL[`dimindex(:N)`;`i'-1`]BITAND_CARD_ODD_EQ_EVEN) THEN
MP_TAC(ARITH_RULE`~(i = i') /\ i = 1 ==> ~(i' = 1)`) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`;ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`] THEN
SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= i  ==> 0 < i `;REAL_ARITH`a - &0 + &0 - a = &0`];ALL_TAC] THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`] THEN
ASM_CASES_TAC`i' = 1` THENL[ASM_SIMP_TAC[ARITH;BITAND_0;EVEN;ODD;SET_RULE`{x |F} = {}`;CARD_CLAUSES] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i-1`]BITAND_CARD_ODD_EQ_EVEN) THEN
MP_TAC(ARITH_RULE`~(i = i') /\ i' = 1 ==> ~(i = 1)`) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`;ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`]
THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= i  ==> 0 < i `;REAL_ARITH`a - a + &0 - &0  = &0`];ALL_TAC]
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`] THEN ASM_CASES_TAC`dimindex(:N) = 1`
THENL[UNDISCH_TAC`i <= 2 EXP dimindex (:N)` THEN UNDISCH_TAC`i' <= 2 EXP dimindex (:N)` THEN
ASM_SIMP_TAC[EXP_1] THEN
REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE`1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`) THEN
MP_TAC(ARITH_RULE`1 <= i' /\ i' <= 2 <=> i' = 1 \/ i' = 2`) THEN ASM_SIMP_TAC[] THEN ASM_ARITH_TAC;ALL_TAC]
THEN MP_TAC(ARITH_RULE`1 <= dimindex(:N) /\ ~(dimindex(:N) = 1) <=> 1 < dimindex(:N)`) THEN
ASM_SIMP_TAC[DIMINDEX_GE_1] THEN REPEAT STRIP_TAC THEN SIMP_TAC[REAL_ARITH`a - a + a - a = &0`];ALL_TAC] THEN
ASM_CASES_TAC`i = i':num` THENL[ASM_SIMP_TAC[]
THEN SIMP_TAC[COND_ID;VSUM_CONST_NUMSEG;ARITH_RULE`(a+1)-1 = a`;COMPLEX_CMUL;GSYM CX_MUL]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
SIMP_TAC[REAL_ARITH`a * &1 / a  =a / a`;GSYM REAL_OF_NUM_POW;POW_REFL];ALL_TAC
] THEN ASM_SIMP_TAC[] THEN SIMP_TAC[FINITE_NUMSEG;VSUM_CASES;NOT_EVEN]
THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
THEN SIMP_TAC[FINITE_NUMSEG;FINITE_RESTRICT;VSUM_CASES;VSUM_CONST] THEN
SIMP_TAC[SET_RULE`{k | k IN {k | k IN t /\ P k} /\ Q k} = {k | k IN t /\  P k /\ Q k}`]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[NOT_EVEN] THEN
SIMP_TAC[COMPLEX_CMUL;GSYM CX_MUL;GSYM CX_ADD;GSYM CX_SUB;GSYM CX_NEG] THEN
AP_TERM_TAC THEN SIMP_TAC[REAL_ARITH`a * b + c * --b = b * (a - c:real)`] THEN
SIMP_TAC[REAL_ARITH`a * --b + c * b = b * (c - a:real)`] THEN
SIMP_TAC[REAL_ARITH`a * b + a * c = a * (b + c:real)`;REAL_ENTIRE] THEN
SUBGOAL_THEN`~(&1 / &(2 EXP dimindex (:N)) = &0)`ASSUME_TAC THENL
[MATCH_MP_TAC REAL_LT_IMP_NZ THEN SIMP_TAC[real_div;REAL_ARITH`&0 < &1 * a <=> &0 < a`]
THEN MATCH_MP_TAC REAL_LT_INV THEN SIMP_TAC[REAL_OF_NUM_LT;SPECL[`dimindex(:N)`;`2`] EXP_LT_0]
THEN ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i - 1`;`i' - 1`]BITAND_CARD_EVEN2_EQ_ODD2) THEN
MP_TAC(SPECL[`dimindex(:N)`;`i - 1`;`i' - 1`]BITAND_CARD_EVEN_ODD_EQ_ODD2)
THEN MP_TAC(SPECL[`dimindex(:N)`;`i - 1`;`i' - 1`]BITAND_CARD_ODD_EVEN_EQ_ODD2) THEN
RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_FINITE_POW;DIMINDEX_2])
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`] THEN
ASM_SIMP_TAC[ ARITH_RULE`1 <= a /\ 1 <= b /\  ~(a = b) ==> ~(a - 1 = b - 1)`]
THEN ASM_CASES_TAC`i = 1` THENL[ASM_SIMP_TAC[ARITH;BITAND_0;EVEN;ODD;SET_RULE`{x |F} = {}`;CARD_CLAUSES]
THEN MP_TAC(SPECL[`dimindex(:N)`;`i'-1`]BITAND_CARD_ODD_EQ_EVEN) THEN
MP_TAC(ARITH_RULE`~(i = i') /\ i = 1 ==> ~(i' = 1)`)
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`;ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`]
THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= i  ==> 0 < i `;REAL_ARITH`a - a + &0 - &0 = &0`];ALL_TAC] THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`] THEN ASM_CASES_TAC`i' = 1` THENL[
ASM_SIMP_TAC[ARITH;BITAND_0;EVEN;ODD;SET_RULE`{x |F} = {}`;CARD_CLAUSES] THEN
MP_TAC(SPECL[`dimindex(:N)`;`i-1`]BITAND_CARD_ODD_EQ_EVEN) THEN
MP_TAC(ARITH_RULE`~(i = i') /\ i' = 1 ==> ~(i = 1)`) THEN
ASM_SIMP_TAC[ARITH_RULE`1 <= i /\ ~(i=1) ==> 0 < i - 1`;ARITH_RULE`1 <= i /\ i <= n ==> i - 1 < n`]
THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= i  ==> 0 < i `;REAL_ARITH`a - &0 + &0 - a = &0`];ALL_TAC]
THEN ASM_SIMP_TAC[ARITH_RULE`1 <= i' /\ ~(i' =1) ==> 0 < i' - 1`] THEN ASM_CASES_TAC`dimindex(:N) = 1`
THENL[UNDISCH_TAC`i <= 2 EXP dimindex (:N)` THEN UNDISCH_TAC`i' <= 2 EXP dimindex (:N)`
THEN ASM_SIMP_TAC[EXP_1] THEN REPEAT STRIP_TAC THEN MP_TAC(ARITH_RULE`1 <= i /\ i <= 2 <=> i = 1 \/ i = 2`)
THEN MP_TAC(ARITH_RULE`1 <= i' /\ i' <= 2 <=> i' = 1 \/ i' = 2`) THEN ASM_SIMP_TAC[]
THEN ASM_ARITH_TAC;ALL_TAC] THEN MP_TAC(ARITH_RULE`1 <= dimindex(:N) /\ ~(dimindex(:N) = 1) <=> 1 < dimindex(:N)`)
THEN ASM_SIMP_TAC[DIMINDEX_GE_1] THEN REPEAT STRIP_TAC THEN SIMP_TAC[REAL_ARITH`a - a + a - a = &0`]
);;

let zero_qstate = new_definition
  `zero_qstate :(N)qstate =
   mk_qstate (lambda i. if i = 1 then Cx(&1) else Cx(&0))`;;

let zero_h = new_definition
`zero_h = cmatrix_qstate_mul (hadamard_n:complex^(2,N)finite_pow^(2,N)finite_pow) (zero_qstate :(N)qstate)`;;

let flip_mat = new_definition
`(flip_mat:num -> complex^(2,N)finite_pow^(2,N)finite_pow) k =
    lambda i j. if (i = k ) /\ (j = k) then --Cx(&1)
                   else if i = j /\ ~(i = k) then Cx(&1)
                   else Cx(&0)`;;

let FLIP_MAT = prove
 (`!n i j.
        1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
        1 <= j /\ j <= dimindex(:(2,N)finite_pow)
        ==> (flip_mat n:complex^(2,N)finite_pow^(2,N)finite_pow)$i$j = if (i = n ) /\ (j = n) then --Cx(&1)
                   else if i = j /\ ~(i = n) then Cx(&1)
                   else Cx(&0)`,
  REPEAT GEN_TAC THEN CHOOSE_TAC (SPEC_ALL FINITE_INDEX_INRANGE)
  THEN ASM_SIMP_TAC[flip_mat;LAMBDA_BETA]);;

let FLIP_DIAGONAL = prove
(`!k.diagonal_cmatrix (flip_mat k:complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[diagonal_cmatrix;flip_mat;LAMBDA_BETA] THEN MESON_TAC[]);;

let FLIP_TRANSP = prove
(`!k.ctransp (flip_mat k:complex^(2,N)finite_pow^(2,N)finite_pow) = flip_mat k`,
SIMP_TAC[FLIP_DIAGONAL;CTRANSP_DIAGONAL_CMATRIX]);;

let FLIP_MAT_HERMITIAN = prove
(`!a. flip_mat a = hermitian_matrix (flip_mat a:complex^(2,N)finite_pow^(2,N)finite_pow)`,
GEN_TAC THEN SIMP_TAC[hermitian_matrix;cmatrix_cnj] THEN
SUBGOAL_THEN `?k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
                    (!A:complex^(2,M)finite_pow^(2,N)finite_pow. A$i = A$k) /\
                      (!z:complex^(2,N)finite_pow. z$i = z$k)`
  CHOOSE_TAC THENL[REWRITE_TAC[FINITE_INDEX_INRANGE2];ALL_TAC] THEN
SUBGOAL_THEN `?l. 1 <= l /\ l <= dimindex(:(2,M)finite_pow) /\
                    (!A:complex^(2,N)finite_pow^(2,M)finite_pow. A$j = A$l) /\
                      (!z:complex^(2,M)finite_pow. z$j = z$l)`
  CHOOSE_TAC THENL[REWRITE_TAC[FINITE_INDEX_INRANGE2];ALL_TAC] THEN
SIMP_TAC[flip_mat] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
ONCE_SIMP_TAC[COND_RAND] THEN ONCE_SIMP_TAC[COND_RAND] THEN ONCE_SIMP_TAC[COND_RAND]
THEN SIMP_TAC[GSYM CX_NEG;CNJ_CX] THEN ASM_MESON_TAC[]);;

let FLIP_MAT_UNITARY = prove
(`!k. unitary_matrix (flip_mat k : complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[unitary_matrix;GSYM FLIP_MAT_HERMITIAN;FLIP_DIAGONAL;CMATRIX_MUL_DIAGONAL]
THEN SIMP_TAC[flip_mat;id_cmatrix] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA]
THEN SIMP_TAC[COND_RMUL;COND_LMUL] THEN
SIMP_TAC[COMPLEX_MUL_RID;COMPLEX_MUL_RZERO;COMPLEX_MUL_RNEG;COMPLEX_NEG_MUL2;COMPLEX_NEG_0]
THEN ASM_MESON_TAC[]);;

let DEST_OF_QSTATE_COMPONENT = prove
 (`!q:complex^(2,N)finite_pow k.
 cnorm2 q = &1
         ==> dest_qstate(mk_qstate q)$k = q$k`,
         SIMP_TAC[GSYM is_qstate;DEST_OF_QSTATE]);;

let IDCMAT_MUL_COMPONENT = prove
(`!i:num q:(N)qstate.
  1 <= i /\ i <= dimindex(:(2,N)finite_pow) ==>
  dest_qstate(id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow ** q)$i = dest_qstate q$i`,
REPEAT STRIP_TAC THEN SIMP_TAC[cmatrix_qstate_mul] THEN
ASSUME_TAC (SPEC_ALL IDCMAT_UNITARY) THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY)) THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE_COMPONENT))
THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;IDCMAT] THEN
SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN
REPEAT STRIP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG]);;

let CMATRIX_QSTATE_MUL_ASSOC = prove
 (`!A B:complex^(2,N)finite_pow^(2,N)finite_pow x:(N)qstate.
    unitary_matrix A /\ unitary_matrix B ==> A ** B ** x = (A ** B) ** x`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY)) THEN
  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY)) THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM is_qstate])
THEN  FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE))
  THEN FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE)) THEN
  SIMP_TAC[cmatrix_mul;cmatrix_qstate_mul] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN SIMP_TAC[FINITE_NUMSEG;GSYM VSUM_COMPLEX_LMUL;GSYM VSUM_COMPLEX_RMUL]
  THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN REPEAT STRIP_TAC THEN
 GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV ) [VSUM_SWAP_NUMSEG] THEN REWRITE_TAC[]);;

let FLIP_COMPONENT = prove
(`!a:num q:(N)qstate.
  1 <= a /\ a <= dimindex(:(2,N)finite_pow) ==>
  dest_qstate(flip_mat a:complex^(2,N)finite_pow^(2,N)finite_pow ** q)$a = --(dest_qstate q$a)`,
REPEAT STRIP_TAC THEN SIMP_TAC[cmatrix_qstate_mul] THEN
ASSUME_TAC (SPEC_ALL FLIP_MAT_UNITARY) THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL UNITARITY)) THEN
FIRST_X_ASSUM(ASSUME_TAC o MATCH_MP (SPEC_ALL DEST_OF_QSTATE_COMPONENT))
THEN ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA;FLIP_MAT] THEN
SIMP_TAC[COND_LMUL;GSYM COMPLEX_NEG_MINUS1;COMPLEX_MUL_LZERO] THEN
SIMP_TAC[VSUM_DELTA_ALT] THEN ASM_SIMP_TAC[IN_NUMSEG]);;

let NHADAMARD_MUL_ZEROQSTATE = prove
(`hadamard_n ** zero_qstate:(N)qstate = mk_qstate(lambda i. Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))`,
SIMP_TAC[cmatrix_qstate_mul;zero_qstate] THEN AP_TERM_TAC THEN
SUBGOAL_THEN`dest_qstate
                   (mk_qstate (lambda i. if i = 1 then Cx (&1) else Cx (&0)))
  = (lambda i. if i = 1 then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow`SUBST1_TAC
THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX]
THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN
SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG;DIMINDEX_GE_1;LE_REFL]
THEN SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 = &1`;
REAL_ARITH` &0 pow 2 = &0`;REAL_ARITH`&1 + &0 = &1`;SQRT_1]
;ALL_TAC] THEN SIMP_TAC[LAMBDA_BETA;COND_RMUL;COMPLEX_MUL_RID;COMPLEX_MUL_RZERO] THEN
SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG;DIMINDEX_GE_1;LE_REFL] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA]
THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
MP_TAC (SPECL[`i:num`;`1`]NHADAMARD_MAT) THEN
ASM_SIMP_TAC[LE_REFL;DIMINDEX_GE_1;ARITH;BITAND_0;EVEN]
);;


(*grover*)
(* tau tau perp*)
let tau = new_definition
  `(tau:num -> (N)qstate) k =
     mk_qstate(lambda i. if i = k then Cx(&1) else Cx(&0))`;;

let TAU_COMPONENT1 = prove
 (`!k i. 1 <= k /\ k <= dimindex (:(2,N)finite_pow) /\ 1 <= i /\ i <= dimindex (:(2,N)finite_pow)
         ==> (dest_qstate (tau i:(N)qstate)$k = if k = i then Cx(&1) else Cx(&0))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[tau] THEN SUBGOAL_THEN`(lambda i'. if i' = i then Cx (&1) else Cx (&0)):complex^(2,N)finite_pow
 = cbasis (i:num)`SUBST1_TAC THENL[SIMP_TAC[cbasis;vector_to_cvector;vector_map;CART_EQ;LAMBDA_BETA;basis] THEN
 ASM_SIMP_TAC[COND_RAND];ALL_TAC] THEN SUBGOAL_THEN`dest_qstate (mk_qstate (cbasis i))
 = cbasis i:complex^(2,N)finite_pow`SUBST1_TAC THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_VECTOR_TO_CVECTOR;cbasis]
 THEN ASM_SIMP_TAC[NORM_BASIS;REAL_ARITH`&1 pow 2 = &1`];ALL_TAC] THEN ASM_SIMP_TAC[CBASIS_COMPONENT]
 );;

let TAU_UNIT = prove
(`!k:num. 1<= k /\ k <= dimindex(:(2,N)finite_pow) ==>
is_qstate ((lambda i. if i = k then Cx(&1) else Cx(&0)):complex^(2,N)finite_pow)`,
REPEAT STRIP_TAC THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;CART_EQ;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN
SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO;VSUM_DELTA_ALT] THEN ASM_SIMP_TAC[IN_NUMSEG]
THEN SIMP_TAC[COMPLEX_NORM_CX; REAL_ARITH`abs (&1) = &1`]);;

(*define outer product*)
let qouter1 = new_definition
  `qouter1 (v:(M)qstate) (w:(N)qstate) :complex^(2,N)finite_pow^(2,M)finite_pow =
     (lambda i j. dest_qstate v$i * cnj (dest_qstate w$j))`;;

(*project*)
let project = new_definition
  `(project:(N)qstate -> complex^(2,N)finite_pow^(2,N)finite_pow) v = qouter1 v v`;;

(*Self-Adjoint*)
let project_HERMITIAN = prove
(`project (v:(N)qstate) = hermitian_matrix (project v)`,
SIMP_TAC[hermitian_matrix;project] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN
REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[qouter1] THEN
ASM_SIMP_TAC[LAMBDA_BETA] THEN SIMP_TAC[CNJ_MUL;CNJ_CNJ;COMPLEX_MUL_AC]);;

let PROJECT_TAU_COMPONENT = prove
(`!k:num.1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
         1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
        1 <= j /\ j <= dimindex(:(2,N)finite_pow)==>
(project (tau k:(N)qstate):complex^(2,N)finite_pow^(2,N)finite_pow)$i$j = if (i = j) /\ (i = k) then Cx(&1) else Cx(&0)`,
SIMP_TAC[project;qouter1;TAU_COMPONENT1;LAMBDA_BETA] THEN SIMP_TAC[COND_LMUL;COND_CNJ;CNJ_CX;COND_RMUL] THEN
SIMP_TAC[COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL[ASM_MESON_TAC[];ALL_TAC]
THEN ASM_MESON_TAC[]
);;

(*Projection: Idempotency*)
let PROJECT_IDEMPOTENT = prove
(`!k:num. 1 <= k /\ k <= dimindex (:(2,N)finite_pow) ==>
   (project (tau k:(N)qstate)) ** project (tau k) = project (tau k)`,
  GEN_TAC THEN SIMP_TAC[cmatrix_mul;LAMBDA_BETA;CART_EQ;PROJECT_TAU_COMPONENT] THEN
  REPEAT STRIP_TAC THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN COND_CASES_TAC THENL[
  ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN
  SIMP_TAC[VSUM_DELTA_ALT] THEN ASM_MESON_TAC[IN_NUMSEG];ALL_TAC] THEN
  GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN ASM_SIMP_TAC[] THEN
  RULE_ASSUM_TAC(SIMP_RULE[DE_MORGAN_THM]) THEN POP_ASSUM MP_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[COND_ID;FINITE_NUMSEG;VSUM_CONST;VSUM_CX;SUM_0]
);;

let cmat_sum = new_definition
    `(cmat_sum:(A->bool)->(A->complex^(2,N)finite_pow^(2,M)finite_pow)->complex^(2,N)finite_pow^(2,M)finite_pow) s f =
      lambda i j. vsum s (\x. f(x)$i$j)`;;

let PROJE_COMPLETE = prove
(`cmat_sum (1..dimindex(:(2,N)finite_pow)) (\i. project(tau i:(N)qstate)) =
  id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow`,
  SIMP_TAC[cmat_sum;id_cmatrix;LAMBDA_BETA;CART_EQ] THEN REPEAT STRIP_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_SIMP_TAC[PROJECT_TAU_COMPONENT] THEN
  COND_CASES_TAC THENL[ASM_SIMP_TAC[] THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)
  [EQ_SYM_EQ] THEN SIMP_TAC[VSUM_DELTA_ALT] THEN ASM_SIMP_TAC[IN_NUMSEG];ALL_TAC] THEN
  GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[VSUM_CX;SUM_0]
);;

let apply_cmatrix = new_definition
  `(apply_cmatrix: complex^(2,N)finite_pow^(2,M)finite_pow -> (N)qstate -> complex^(2,M)finite_pow) A q  =
   lambda i. vsum (1..dimindex (:(2,N)finite_pow)) (\j. A$i$j * dest_qstate q$j)`;;

let measurement = new_definition
`!x y:(N)qstate.
  measurement x y = cnorm2(apply_cmatrix (project x) y) `;;

let tau_perp = new_definition
  `(tau_perp: num -> (N)qstate) k =
    mk_qstate (lambda i. if i = k then Cx(&0) else Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow)) - &1)))`;;

let TAU_PERP_UNIT = prove
(`!k:num. 1<= k /\ k <= dimindex(:(2,N)finite_pow) ==>is_qstate
  ((lambda i. if i = k
        then Cx (&0) else Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow)) - &1))):complex^(2,N)finite_pow)`,
REPEAT STRIP_TAC THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;CART_EQ;LAMBDA_BETA;COND_CNJ;CNJ_CX] THEN
SIMP_TAC[COND_LMUL;COMPLEX_MUL_LZERO;GSYM CX_MUL] THEN SIMP_TAC[real_div;REAL_MUL_LID;GSYM REAL_INV_MUL]
THEN SIMP_TAC[GSYM SQRT_MUL;GSYM REAL_POW_2;POW_2_SQRT_ABS]
THEN SUBGOAL_THEN`abs (&(dimindex (:(2,N)finite_pow)) - &1) = &(dimindex (:(2,N)finite_pow)) - &1` SUBST1_TAC THENL[
SIMP_TAC[REAL_ABS_REFL] THEN ONCE_SIMP_TAC[REAL_ARITH`a <= b <=> a  + &1<= b + &1`] THEN
SIMP_TAC[REAL_ARITH`a - &1  + &1 = a`;REAL_ARITH`&0 + &1 = &1`] THEN SIMP_TAC[REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC]
THEN SIMP_TAC[VSUM_CASES;FINITE_NUMSEG] THEN REPEAT (POP_ASSUM MP_TAC)
THEN SIMP_TAC[GSYM IMP_CONJ;GSYM IN_NUMSEG] THEN SIMP_TAC[SET_RULE`k IN 1.. dimindex(:(2,N)finite_pow) ==>
    {i | i IN 1.. dimindex(:(2,N)finite_pow) /\ i = k} = {k}`] THEN SIMP_TAC[VSUM_SING;COMPLEX_ADD_LID] THEN
SIMP_TAC[SET_RULE`{i |i IN s /\ ~(i = k)} = {i | i IN s} DIFF {i |i IN s /\ i = k}`] THEN
SUBGOAL_THEN`vsum
      ({i | i IN 1..dimindex (:(2,N)finite_pow)} DIFF
       {i | i IN 1..dimindex (:(2,N)finite_pow) /\ i = k})
     (\i. Cx (inv (&(dimindex (:(2,N)finite_pow)) - &1))) = vsum
      ({i | i IN 1..dimindex (:(2,N)finite_pow)})
     (\i. Cx (inv (&(dimindex (:(2,N)finite_pow)) - &1))) - vsum
      ({i | i IN 1..dimindex (:(2,N)finite_pow) /\ i = k})
     (\i. Cx (inv (&(dimindex (:(2,N)finite_pow)) - &1)))`SUBST1_TAC THENL[MATCH_MP_TAC VSUM_DIFF
THEN SIMP_TAC[SET_RULE` {i |i IN s /\ i = k} SUBSET  {i | i IN s}`]
THEN SIMP_TAC[SET_RULE`{i | i IN 1.. n} = (1..n)`;FINITE_NUMSEG];ALL_TAC] THEN
SIMP_TAC[SET_RULE`k IN 1.. n ==> {i |i IN 1..n /\ i = k } = {k}`;SET_RULE`{i | i IN 1.. n} = (1..n)`;
FINITE_NUMSEG;VSUM_CONST;VSUM_SING;CARD_NUMSEG_1;COMPLEX_CMUL;SIMPLE_COMPLEX_ARITH`a * b - b = (a - Cx(&1)) * b`]
THEN SIMP_TAC[GSYM CX_SUB;GSYM CX_MUL;COMPLEX_NORM_CX] THEN STRIP_TAC THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
THEN MP_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN SIMP_TAC[DIMINDEX_GE_1] THEN STRIP_TAC THEN
ASM_SIMP_TAC[REAL_OF_NUM_SUB] THEN RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_CLAUSES]) THEN
SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN ASM_SIMP_TAC[REAL_ARITH`&2 <= a ==> ~(a - &1 = &0)`;REAL_MUL_RINV]
THEN SIMP_TAC[REAL_ABS_1]);;

let TAU_PERP_COMPONENT1 = prove
 (`!k i. 1 <= k /\ k <= dimindex (:(2,N)finite_pow) /\ 1 <= i /\ i <= dimindex (:(2,N)finite_pow)
         ==> (dest_qstate (tau_perp i:(N)qstate)$k = if k = i then Cx(&0) else Cx(&1 / sqrt(&(dimindex(:(2,N)finite_pow)) - &1)))`,
  REPEAT STRIP_TAC THEN SIMP_TAC[tau_perp] THEN SUBGOAL_THEN `dest_qstate(mk_qstate((lambda i'. if i' = i
   then Cx (&0) else Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow)) - &1))):complex^(2,N)finite_pow))
= (lambda i'. if i' = i then Cx (&0) else Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow)) - &1))):complex^(2,N)finite_pow`
SUBST1_TAC THENL[ MATCH_MP_TAC DEST_OF_QSTATE THEN ASM_SIMP_TAC[TAU_PERP_UNIT];ALL_TAC] THEN
ASM_SIMP_TAC[CART_EQ;LAMBDA_BETA]);;

(*define Uf= I - 2|τ><τ| D = 2|φ><φ| - I G = D*U*)
let U = new_definition
`(U:num -> complex^(2,N)finite_pow^(2,N)finite_pow) k = id_cmatrix - Cx(&2) %* project (tau k)`;;

let D = new_definition
`D:complex^(2,N)finite_pow^(2,N)finite_pow = Cx(&2) %* project zero_h - id_cmatrix`;;

let G = new_definition
`(G:num -> complex^(2,N)finite_pow^(2,N)finite_pow) k = D ** (U k)`;;

let U_EQ_FLIPMAT = prove
(`!k:num. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) ==>
U k:complex^(2,N)finite_pow^(2,N)finite_pow = flip_mat k:complex^(2,N)finite_pow^(2,N)finite_pow`,
SIMP_TAC[U;cmatrix_sub;flip_mat;IDCMAT;LAMBDA_BETA;CART_EQ;cmatrix_cmul;PROJECT_TAU_COMPONENT]
THEN SIMP_TAC[COND_RMUL;COMPLEX_MUL_RID;COMPLEX_MUL_RZERO] THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL[
ASM_SIMP_TAC[] THEN COND_CASES_TAC THENL[SIMP_TAC[SIMPLE_COMPLEX_ARITH`Cx(&1) - Cx(&2) = --Cx(&1)`];ALL_TAC]
THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`Cx(&1) - Cx(&0) = Cx(&1)`];ALL_TAC] THEN SIMP_TAC[COND_RAND] THEN
SIMP_TAC[SIMPLE_COMPLEX_ARITH`Cx(&0) - Cx(&0) = Cx(&0)`] THEN COND_CASES_TAC THENL[ASM_MESON_TAC[];ALL_TAC]
THEN SIMPLE_COMPLEX_ARITH_TAC
);;

let U_HERMITIAN = prove
(`U (k:num) = hermitian_matrix ((U k):complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[U;HERMITIAN_SUB;GSYM IDCMAT_HERMITIAN;HERMITIAN_CMUL;CNJ_CX;GSYM project_HERMITIAN]);;

let U_UNITARY = prove
(`unitary_matrix (U (k:num):complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[unitary_matrix;GSYM U_HERMITIAN;U;CMATRIX_SUB_RDISTRIB;CMATRIX_SUB_LDISTRIB;IDCMAT_MUL_MAT;MAT_MUL_IDCMAT]
THEN SIMP_TAC[cmatrix_sub;cmatrix_add;LAMBDA_BETA;CART_EQ] THEN
SIMP_TAC[cmatrix_cmul;SIMPLE_COMPLEX_ARITH`a-b-(b-d:complex)=a-Cx(&2)*b+d`]
THEN SIMP_TAC[LAMBDA_BETA;SIMPLE_COMPLEX_ARITH`Cx(&2)*Cx(&2)*b=Cx(&4)*b`]THEN SIMP_TAC[cmatrix_mul;LAMBDA_BETA;SIMPLE_COMPLEX_ARITH`(Cx(&2)*b)*Cx(&2)*c=Cx(&4)*b*c`]
THEN SIMP_TAC[VSUM_COMPLEX_LMUL;FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`a - Cx(&4)*b + Cx(&4)*c = a <=> b = c`]
THEN ASM_SIMP_TAC[project;qouter1;LAMBDA_BETA] THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`(a*b)*c*d=(a*d)*(c*b:complex)`]
THEN SIMP_TAC[VSUM_COMPLEX_LMUL;FINITE_NUMSEG] THEN SUBGOAL_THEN` vsum (1..dimindex (:(2,N)finite_pow))
 (\k'. dest_qstate ((tau k):(N)qstate)$k' * cnj (dest_qstate ((tau k):(N)qstate)$k')) = Cx(&1) `SUBST1_TAC
 THENL[ASSUME_TAC  (SPEC`tau:(N)qstate` QSTATE_NORM) THEN SIMP_TAC[GSYM cdot;GSYM CX_CNORM2] THEN
 AP_TERM_TAC THEN ASM_SIMP_TAC[];ALL_TAC] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let U_PHASE_FLIP = prove
(`!k:num a b:real. 1 <= k /\ k <= dimindex (:(2,N)finite_pow) /\
 a pow 2 + b pow 2 = &1 ==> (U k:complex^(2,N)finite_pow^(2,N)finite_pow) **
     (mk_qstate (Cx(a) %%% (tau k:(N)qstate) + Cx(b) %%% (tau_perp k:(N)qstate))):(N)qstate
      = (mk_qstate(Cx(b) %%% (tau_perp k:(N)qstate) - Cx(a) %%% (tau k:(N)qstate))):(N)qstate`,
  REPEAT STRIP_TAC THEN SIMP_TAC[cmatrix_qstate_mul] THEN AP_TERM_TAC
  THEN SUBGOAL_THEN`dest_qstate
  (mk_qstate (Cx a %%% (tau k:(N)qstate) + Cx b %%% (tau_perp k:(N)qstate))) =
  (Cx a %%% (tau k:(N)qstate) + Cx b %%% (tau_perp k:(N)qstate)):complex^(2,N)finite_pow`SUBST1_TAC
THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;qstate_cmul;tau;tau_perp]
THEN ASM_SIMP_TAC[TAU_UNIT;TAU_PERP_UNIT;DEST_OF_QSTATE] THEN SIMP_TAC[LAMBDA_BETA;CART_EQ;CVECTOR_ADD_COMPONENT]
THEN SIMP_TAC[COND_RMUL;COMPLEX_MUL_RZERO;COMPLEX_MUL_RID] THEN SIMP_TAC[COND_RAND;COMPLEX_ADD_RID;COMPLEX_ADD_LID;CNJ_CX;GSYM CX_MUL]
THEN SIMP_TAC[GSYM REAL_POW_2;VSUM_CASES;FINITE_NUMSEG] THEN UNDISCH_TAC`k <= dimindex (:(2,N)finite_pow)` THEN
UNDISCH_TAC`1 <= k` THEN SIMP_TAC[GSYM IN_NUMSEG;GSYM IMP_CONJ] THEN SIMP_TAC[SET_RULE`k IN 1.. dimindex(:(2,N)finite_pow) ==>
    {i | i IN 1.. dimindex(:(2,N)finite_pow) /\ i = k} = {k}`] THEN SIMP_TAC[VSUM_SING] THEN
SIMP_TAC[SET_RULE`{i |i IN s /\ ~(i = k)} = {i | i IN s} DIFF {i |i IN s /\ i = k}`] THEN
SIMP_TAC[SET_RULE` {i |i IN s /\ i = k} SUBSET  {i | i IN s}`;SET_RULE`{i | i IN 1.. n} = (1..n)`;FINITE_NUMSEG;VSUM_DIFF]
THEN SIMP_TAC[SET_RULE`k IN 1.. n ==> {i |i IN 1..n /\ i = k } = {k}`;FINITE_NUMSEG;VSUM_CONST;VSUM_SING;CARD_NUMSEG_1] THEN
SIMP_TAC[REAL_POW_MUL;REAL_POW_DIV;REAL_POW_ONE;REAL_SQRT_POW_2;COMPLEX_CMUL;SIMPLE_COMPLEX_ARITH`a * b - b = (a - Cx(&1)) * b`]
THEN SIMP_TAC[GSYM CX_SUB;GSYM CX_MUL] THEN SUBGOAL_THEN`abs (&(dimindex (:(2,N)finite_pow)) - &1) = &(dimindex (:(2,N)finite_pow)) - &1`
ASSUME_TAC THENL[SIMP_TAC[REAL_ABS_REFL;REAL_ARITH`&0 <= a - &1 <=> &1 <= a`;REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC] THEN
SUBGOAL_THEN`~(&(dimindex (:(2,N)finite_pow)) - &1 = &0)`ASSUME_TAC THENL[SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;
REAL_ARITH`a - &1 = &0 <=> a = &1`] THEN SIMP_TAC[GSYM  REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC (REAL_ARITH`&2 <= a ==> ~(a = &1)`)
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[REAL_ARITH`&2 = &2 pow 1`] THEN MATCH_MP_TAC REAL_POW_MONO THEN
SIMP_TAC[DIMINDEX_GE_1] THEN REAL_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[REAL_FIELD`~(a = &0) ==> a * b * &1 / a = b`] THEN
ASM_SIMP_TAC[GSYM CX_ADD;COMPLEX_NORM_CX] THEN REAL_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[U_EQ_FLIPMAT;FLIP_MAT;CART_EQ;LAMBDA_BETA]
THEN SIMP_TAC[COND_LMUL;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
ASM_CASES_TAC`i = k:num` THENL[ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG;CVECTOR_ADD_COMPONENT] THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`
--Cx(&1) * (a + b) = --b - a`] THEN ASM_SIMP_TAC[CVECTOR_SUB_COMPONENT;SIMPLE_COMPLEX_ARITH`--a - b = a - b <=> a = Cx(&0)`]
THEN SIMP_TAC[qstate_cmul] THEN ASM_SIMP_TAC[TAU_PERP_COMPONENT1;LAMBDA_BETA] THEN SIMPLE_COMPLEX_ARITH_TAC;ALL_TAC] THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN ASM_SIMP_TAC[VSUM_DELTA_ALT;IN_NUMSEG;CVECTOR_ADD_COMPONENT] THEN
ASM_SIMP_TAC[CVECTOR_SUB_COMPONENT;SIMPLE_COMPLEX_ARITH`a + b = b - a <=> a = Cx(&0)`] THEN SIMP_TAC[qstate_cmul] THEN ASM_SIMP_TAC[TAU_COMPONENT1;LAMBDA_BETA] THEN SIMPLE_COMPLEX_ARITH_TAC
);;

let D_COMPONENT = prove
(`!i j.
  1 <= i /\ i <= dimindex(:(2,N)finite_pow) /\
  1 <= j /\ j <= dimindex(:(2,N)finite_pow)
  ==> (D:complex^(2,N)finite_pow^(2,N)finite_pow )$i$j = if i = j then Cx(&2 / &(dimindex(:(2,N)finite_pow)) - &1)
  else Cx(&2 / &(dimindex(:(2,N)finite_pow)))`,
  SIMP_TAC[D;zero_h;NHADAMARD_MUL_ZEROQSTATE;project;qouter1] THEN
  SUBGOAL_THEN`dest_qstate(mk_qstate (lambda i. Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow))))))
= (lambda i. Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow))))):complex^(2,N)finite_pow`SUBST1_TAC
THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX]
THEN SIMP_TAC[GSYM CX_MUL;GSYM REAL_POW_2;ONE_DIV_SQRTN;DIMINDEX_GE_1] THEN
SIMP_TAC[VSUM_CONST_NUMSEG;ADD_SUB;COMPLEX_CMUL;GSYM CX_MUL] THEN
SIMP_TAC[REAL_ARITH`a * &1 / a = a / a`;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_POW;POW_REFL]
THEN SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC] THEN
SIMP_TAC[GSYM vector_const] THEN SIMP_TAC[VECTOR_CONST_COMPONENT;CNJ_CX] THEN SIMP_TAC[GSYM CX_MUL;
REAL_ARITH`a * a:real = a pow 2`] THEN SIMP_TAC[ONE_DIV_SQRTN;DIMINDEX_GE_1] THEN SIMP_TAC[cmatrix_cmul]
THEN SIMP_TAC[CMATRIX_SUB_COMPONENT] THEN SIMP_TAC[LAMBDA_BETA;IDCMAT] THEN
SIMP_TAC[GSYM CX_MUL;REAL_ARITH`&2 * &1 / a = &2 / a`]
THEN SIMP_TAC[COND_RAND;COMPLEX_SUB_RZERO] THEN SIMP_TAC[CX_SUB] THEN MESON_TAC[]
);;

let D_HERMITIAN = prove
(`D:complex^(2,N)finite_pow^(2,N)finite_pow = hermitian_matrix D`,
SIMP_TAC[D;HERMITIAN_SUB;GSYM IDCMAT_HERMITIAN;HERMITIAN_CMUL;CNJ_CX;GSYM project_HERMITIAN]);;

let D_UNITARY = prove
(`unitary_matrix (D:complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[unitary_matrix;GSYM D_HERMITIAN;D;CMATRIX_SUB_RDISTRIB;CMATRIX_SUB_LDISTRIB;IDCMAT_MUL_MAT;MAT_MUL_IDCMAT]
THEN SIMP_TAC[cmatrix_sub;cmatrix_add;LAMBDA_BETA;CART_EQ] THEN
SIMP_TAC[cmatrix_cmul;SIMPLE_COMPLEX_ARITH`a-b-(b-d:complex)=a-Cx(&2)*b+d`]
THEN SIMP_TAC[LAMBDA_BETA;SIMPLE_COMPLEX_ARITH`Cx(&2)*Cx(&2)*b=Cx(&4)*b`]THEN SIMP_TAC[cmatrix_mul;LAMBDA_BETA;SIMPLE_COMPLEX_ARITH`(Cx(&2)*b)*Cx(&2)*c=Cx(&4)*b*c`]
THEN SIMP_TAC[VSUM_COMPLEX_LMUL;FINITE_NUMSEG] THEN REPEAT STRIP_TAC THEN
AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`Cx(&4)*b-Cx(&4)*c+a = a <=> b = c`]
THEN ASM_SIMP_TAC[project;qouter1;LAMBDA_BETA] THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`(a*b)*c*d=(a*d)*(c*b:complex)`]
THEN SIMP_TAC[VSUM_COMPLEX_LMUL;FINITE_NUMSEG] THEN SUBGOAL_THEN` vsum (1..dimindex (:(2,N)finite_pow))
 (\k. dest_qstate (zero_h:(N)qstate)$k * cnj (dest_qstate (zero_h:(N)qstate)$k)) = Cx(&1) `SUBST1_TAC
 THENL[SIMP_TAC[zero_h;NHADAMARD_MUL_ZEROQSTATE] THEN SUBGOAL_THEN`dest_qstate(mk_qstate (lambda i. Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow))))))
= (lambda i. Cx(&1 / sqrt (&(dimindex (:(2,N)finite_pow))))):complex^(2,N)finite_pow`SUBST1_TAC
THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;LAMBDA_BETA;COND_CNJ;CNJ_CX]
THEN SIMP_TAC[GSYM CX_MUL;GSYM REAL_POW_2;ONE_DIV_SQRTN;DIMINDEX_GE_1] THEN
SIMP_TAC[VSUM_CONST_NUMSEG;ADD_SUB;COMPLEX_CMUL;GSYM CX_MUL] THEN
SIMP_TAC[REAL_ARITH`a * &1 / a = a / a`;DIMINDEX_FINITE_POW;DIMINDEX_2;GSYM REAL_OF_NUM_POW;POW_REFL]
THEN SIMP_TAC[complex_norm;RE_CX;IM_CX;REAL_ARITH`&1 pow 2 + &0 pow 2 = &1`;SQRT_1];ALL_TAC] THEN
ASM_SIMP_TAC[LAMBDA_BETA;CNJ_CX;GSYM CX_MUL] THEN SIMP_TAC[REAL_ARITH`a*a:real = a pow 2`]
THEN SIMP_TAC[ONE_DIV_SQRTN;DIMINDEX_GE_1] THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;FINITE_NUMSEG;VSUM_CONST]
THEN SIMP_TAC[CARD_NUMSEG_1;COMPLEX_CMUL;GSYM CX_MUL;REAL_ARITH`a * &1 / a = a / a`] THEN AP_TERM_TAC THEN
SUBGOAL_THEN`&0 < &(2 EXP dimindex (:N))`ASSUME_TAC THENL[ASSUME_TAC (SPECL[`dimindex(:N):num`;`2`] (GSYM EXP_LT_0))
THEN RULE_ASSUM_TAC(REWRITE_RULE[ARITH_RULE`~(2=0)`]) THEN ASM_REWRITE_TAC[REAL_OF_NUM_LT];ALL_TAC]
THEN ASM_SIMP_TAC[REAL_FIELD`&0 < a ==> a / a = &1`];ALL_TAC] THEN
SIMPLE_COMPLEX_ARITH_TAC);;

let G_UNITARY = prove
(`unitary_matrix (G k:complex^(2,N)finite_pow^(2,N)finite_pow)`,
SIMP_TAC[G;UNITARY_MUL;D_UNITARY;U_UNITARY]
);;

let cmatrix_pow = define
    `((cmatrix_pow: complex^(2,N)finite_pow^(2,N)finite_pow->num->complex^(2,N)finite_pow^(2,N)finite_pow) A 0 =
    (id_cmatrix :complex^(2,N)finite_pow^(2,N)finite_pow)) /\ (cmatrix_pow A (SUC n) = A ** (cmatrix_pow A n))`;;

parse_as_infix("cmatrix_pow",(200,"right"));;

let CMATRIX_POW_1 = prove
    (`!A:complex^(2,N)finite_pow^(2,N)finite_pow. A cmatrix_pow 1 = A`,
     REWRITE_TAC[num_CONV `1`] THEN SIMP_TAC[cmatrix_pow;MAT_MUL_IDCMAT]);;

let CMATRIX_POW_2 =  prove
    (`!A:complex^(2,N)finite_pow^(2,N)finite_pow. A cmatrix_pow 2 = A ** A`,
    SIMP_TAC[cmatrix_pow;num_CONV `2`;CMATRIX_POW_1]);;

let CMATRIX_POW_3 =  prove
    (`!A:complex^(2,N)finite_pow^(2,N)finite_pow. A cmatrix_pow 3 = A ** A ** A`,
    SIMP_TAC[cmatrix_pow;num_CONV `3`;num_CONV `2`;CMATRIX_POW_1]);;

let CMATRIX_POW_ONE = prove
    (`!n. (id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow) cmatrix_pow n = (id_cmatrix:complex^(2,N)finite_pow^(2,N)finite_pow)`,
     INDUCT_TAC THEN ASM_SIMP_TAC [cmatrix_pow;IDCMAT_MUL_MAT]);;

let CMATRIX_POW_ADD = prove
    (`!A:complex^(2,N)finite_pow^(2,N)finite_pow m n. A cmatrix_pow (m + n) = (A cmatrix_pow m) ** (A cmatrix_pow n)`,
     GEN_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC[cmatrix_pow; ADD_CLAUSES; IDCMAT_MUL_MAT] THEN REWRITE_TAC[CMATRIX_MUL_ASSOC]);;

let UNITARY_POW = prove
(`!A:complex^(2,N)finite_pow^(2,N)finite_pow n:num. unitary_matrix A ==> unitary_matrix(A cmatrix_pow n)`,
GEN_TAC THEN INDUCT_TAC THENL[SIMP_TAC[cmatrix_pow;IDCMAT_UNITARY];ALL_TAC] THEN SIMP_TAC[cmatrix_pow]
THEN ASM_SIMP_TAC[UNITARY_MUL]
);;

let ZERO_STATE_DECOMPOSITION = prove
(`!k:num. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) ==>
 zero_h:(N)qstate = mk_qstate(
Cx(sin (asn(&1 / sqrt(&(dimindex(:(2,N)finite_pow)))))) %%% ((tau k):(N)qstate) +
Cx(cos (asn(&1 / sqrt(&(dimindex(:(2,N)finite_pow)))))) %%% ((tau_perp k):(N)qstate))`,
REPEAT STRIP_TAC THEN SIMP_TAC[zero_h;NHADAMARD_MUL_ZEROQSTATE;DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
AP_TERM_TAC THEN SUBGOAL_THEN`sin (asn (&1 / sqrt (&(2 EXP dimindex (:N))))) = &1 / sqrt (&(2 EXP dimindex (:N)))`ASSUME_TAC
THENL[MATCH_MP_TAC SIN_ASN THEN STRIP_TAC THENL[SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
ASSUME_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_GE_1]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_LE]) THEN MP_TAC (REAL_ARITH`&2 <= &(2 EXP dimindex (:N)) ==> &0 < &(2 EXP dimindex (:N))`)
THEN ASM_SIMP_TAC[] THEN ONCE_SIMP_TAC[GSYM REAL_LT_INV_EQ] THEN ONCE_SIMP_TAC[GSYM SQRT_LT_0] THEN
SIMP_TAC[REAL_ARITH`&0 < a ==> -- &1 <= a`];ALL_TAC] THEN SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM SQRT_1] THEN SIMP_TAC[SQRT_MONO_LE_EQ] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
SIMP_TAC[REAL_ARITH`&0 < &1`] THEN ASSUME_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_GE_1]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_LE]) THEN MP_TAC (REAL_ARITH`&2 <= &(2 EXP dimindex (:N)) ==> &1 <= &(2 EXP dimindex (:N))`)
THEN ASM_SIMP_TAC[];ALL_TAC] THEN SUBGOAL_THEN`cos (asn (&1 / sqrt (&(2 EXP dimindex (:N))))) =
 sqrt(&1 - (&1 / sqrt (&(2 EXP dimindex (:N)))) pow 2)`SUBST1_TAC THENL[MATCH_MP_TAC COS_ASN THEN
 STRIP_TAC THENL[SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
ASSUME_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_GE_1]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_LE]) THEN MP_TAC (REAL_ARITH`&2 <= &(2 EXP dimindex (:N)) ==> &0 < &(2 EXP dimindex (:N))`)
THEN ASM_SIMP_TAC[] THEN ONCE_SIMP_TAC[GSYM REAL_LT_INV_EQ] THEN ONCE_SIMP_TAC[GSYM SQRT_LT_0] THEN
SIMP_TAC[REAL_ARITH`&0 < a ==> -- &1 <= a`];ALL_TAC] THEN SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM SQRT_1] THEN SIMP_TAC[SQRT_MONO_LE_EQ] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
SIMP_TAC[REAL_ARITH`&0 < &1`] THEN ASSUME_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_GE_1]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_LE]) THEN MP_TAC (REAL_ARITH`&2 <= &(2 EXP dimindex (:N)) ==> &1 <= &(2 EXP dimindex (:N))`)
THEN ASM_SIMP_TAC[];ALL_TAC] THEN ASM_SIMP_TAC[qstate_cmul] THEN SUBGOAL_THEN`(lambda i. Cx (&1 / sqrt (&(2 EXP dimindex (:N)))) *
dest_qstate (tau k:(N)qstate)$i):complex^(2,N)finite_pow = (lambda i. Cx (&1 / sqrt (&(2 EXP dimindex (:N)))) *
(if i = k then Cx (&1) else Cx (&0))):complex^(2,N)finite_pow`SUBST1_TAC THENL[ASM_SIMP_TAC[TAU_COMPONENT1;CART_EQ;LAMBDA_BETA];ALL_TAC]
THEN SIMP_TAC[CART_EQ;LAMBDA_BETA] THEN REPEAT STRIP_TAC THEN SUBGOAL_THEN`(lambda i. Cx (sqrt (&1 - (&1 / sqrt (&(2 EXP dimindex (:N)))) pow 2))
* dest_qstate (tau_perp k:(N)qstate)$i):complex^(2,N)finite_pow = (lambda i. Cx (sqrt (&1 - (&1 / sqrt (&(2 EXP dimindex (:N)))) pow 2)) *
(if i = k then Cx (&0) else Cx (&1 / sqrt (&(dimindex (:(2,N)finite_pow)) - &1)))):complex^(2,N)finite_pow`SUBST1_TAC THENL[ASM_SIMP_TAC[TAU_PERP_COMPONENT1;CART_EQ;LAMBDA_BETA];ALL_TAC] THEN SIMP_TAC[COND_RMUL;COMPLEX_MUL_RID;COMPLEX_MUL_RZERO]
THEN AP_THM_TAC THEN AP_TERM_TAC THEN SIMP_TAC[GSYM CX_MUL] THEN SUBGOAL_THEN`sqrt (&1 - (&1 / sqrt (&(2 EXP dimindex (:N)))) pow 2) *
&1 / sqrt (&(dimindex (:(2,N)finite_pow)) - &1) = &1 / sqrt (&(2 EXP dimindex (:N)))`SUBST1_TAC THENL[SIMP_TAC[REAL_ARITH`a * &1 / b = a / b`;
GSYM SQRT_DIV] THEN SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV;SQRT_INJ;DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
SUBGOAL_THEN`sqrt (inv (&(2 EXP dimindex (:N)))) pow 2 = inv (&(2 EXP dimindex (:N)))`SUBST1_TAC THENL[MATCH_MP_TAC SQRT_POW_2
THEN SIMP_TAC[REAL_LE_INV_EQ] THEN SIMP_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;ALL_TAC] THEN
SUBGOAL_THEN`(&1 - inv (&(2 EXP dimindex (:N)))) = (&(2 EXP dimindex (:N)) - &1 ) / (&1 * &(2 EXP dimindex (:N)))`SUBST1_TAC
THENL[GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_SUB_INV THEN
SIMP_TAC[REAL_ARITH`~(&1 = &0)`] THEN SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
MP_TAC (SPECL[`&2`;`dimindex(:N)`]REAL_POW_LT) THEN SIMP_TAC[REAL_ARITH`&0 < &2`] THEN REAL_ARITH_TAC;ALL_TAC] THEN
SIMP_TAC[REAL_MUL_LID;real_div] THEN ONCE_SIMP_TAC[REAL_ARITH`(a * inv (b)) * inv(a) = (a * inv(a)) * inv(b):real`]
THEN SUBGOAL_THEN`(&(2 EXP dimindex (:N)) - &1) * inv (&(2 EXP dimindex (:N)) - &1) = &1`SUBST1_TAC THENL[MATCH_MP_TAC REAL_MUL_RINV
THEN SIMP_TAC[REAL_ARITH`~(a - &1 = &0) <=> ~(a = &1)`] THEN SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC
(REAL_ARITH`&2 <= a ==> ~(a = &1)`) THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV) [REAL_ARITH`&2 = &2 pow 1`] THEN
MATCH_MP_TAC REAL_POW_MONO THEN SIMP_TAC[DIMINDEX_GE_1] THEN REAL_ARITH_TAC;ALL_TAC] THEN REAL_ARITH_TAC;ALL_TAC]
THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;CVECTOR_ADD_COMPONENT] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
ASM_SIMP_TAC[LAMBDA_BETA]  THEN SIMP_TAC[COND_RAND] THEN SIMPLE_COMPLEX_ARITH_TAC
);;

let GROVER_ITER = prove
(`!k t:num. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) ==>
(((G k):complex^(2,N)finite_pow^(2,N)finite_pow) cmatrix_pow t) ** zero_h:(N)qstate = mk_qstate(
    Cx(sin((&2 * &t + &1) * asn(&1 / sqrt(&(dimindex(:(2,N)finite_pow)))))) %%% ((tau k):(N)qstate) +
    Cx(cos((&2 * &t + &1) * asn(&1 / sqrt(&(dimindex(:(2,N)finite_pow)))))) %%% ((tau_perp k):(N)qstate))`,
 GEN_TAC THEN INDUCT_TAC THENL [SIMP_TAC[cmatrix_pow;IDCMAT_MUL_QSTATE] THEN
SIMP_TAC[REAL_ARITH`&2 * &0 + &1 = &1`;REAL_ARITH`&1 * a = a`] THEN SIMP_TAC[ZERO_STATE_DECOMPOSITION];ALL_TAC]
THEN SIMP_TAC[cmatrix_pow] THEN ASM_SIMP_TAC[G_UNITARY;UNITARY_POW;GSYM CMATRIX_QSTATE_MUL_ASSOC] THEN
SIMP_TAC[G] THEN SIMP_TAC[U_UNITARY;D_UNITARY;GSYM CMATRIX_QSTATE_MUL_ASSOC] THEN STRIP_TAC THEN
SUBGOAL_THEN`(U k:complex^(2,N)finite_pow^(2,N)finite_pow) **
     (mk_qstate
     (Cx(sin((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) %%%
      (tau k:(N)qstate) +
      Cx(cos((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) %%%
      (tau_perp k:(N)qstate))):(N)qstate = (mk_qstate(Cx(cos((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) %%%
      (tau_perp k:(N)qstate) -
      Cx(sin((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) %%%
      (tau k:(N)qstate))):(N)qstate
      `SUBST1_TAC THENL[MATCH_MP_TAC (SPECL[`k:num`;`sin ((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))`;
      `cos ((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))`] U_PHASE_FLIP) THEN ASM_SIMP_TAC[SIN_CIRCLE];ALL_TAC]
THEN SIMP_TAC[cmatrix_qstate_mul] THEN AP_TERM_TAC THEN SUBGOAL_THEN ` dest_qstate
                 (mk_qstate (Cx (cos ((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) %%% (tau_perp k:(N)qstate) -
                  Cx (sin ((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) %%% (tau k:(N)qstate))) =
                (Cx (cos ((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) %%% (tau_perp k:(N)qstate) -
Cx (sin ((&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) %%% (tau k:(N)qstate)):complex^(2,N)finite_pow`SUBST1_TAC
THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;qstate_cmul;tau;tau_perp] THEN ASM_SIMP_TAC[TAU_UNIT;TAU_PERP_UNIT;DEST_OF_QSTATE] THEN SIMP_TAC[LAMBDA_BETA;CART_EQ;CVECTOR_SUB_COMPONENT] THEN
SIMP_TAC[COND_RMUL;COMPLEX_MUL_RZERO;COMPLEX_MUL_RID] THEN SIMP_TAC[COND_RAND;COMPLEX_SUB_LZERO;COMPLEX_SUB_RZERO] THEN
SIMP_TAC[GSYM CX_MUL;CNJ_CX;CNJ_NEG;COMPLEX_NEG_MUL2] THEN SIMP_TAC[REAL_ARITH`x * x:real = x pow 2`] THEN
SIMP_TAC[VSUM_CASES;FINITE_NUMSEG] THEN UNDISCH_TAC`k <= dimindex (:(2,N)finite_pow)` THEN
UNDISCH_TAC`1 <= k` THEN SIMP_TAC[GSYM IN_NUMSEG;GSYM IMP_CONJ] THEN SIMP_TAC[SET_RULE`k IN 1.. dimindex(:(2,N)finite_pow) ==>
    {i | i IN 1.. dimindex(:(2,N)finite_pow) /\ i = k} = {k}`] THEN SIMP_TAC[VSUM_SING] THEN SIMP_TAC[SET_RULE`{i |i IN s /\ ~(i = k)}
  = {i | i IN s} DIFF {i |i IN s /\ i = k}`] THEN SIMP_TAC[SET_RULE` {i |i IN s /\ i = k} SUBSET  {i | i IN s}`;SET_RULE`{i | i IN 1.. n}
  = (1..n)`;FINITE_NUMSEG;VSUM_DIFF] THEN SIMP_TAC[SET_RULE`k IN 1.. n ==> {i |i IN 1..n /\ i = k } = {k}`;FINITE_NUMSEG;VSUM_CONST;VSUM_SING;CARD_NUMSEG_1] THEN SIMP_TAC[REAL_POW_MUL;REAL_POW_DIV;REAL_POW_ONE;REAL_SQRT_POW_2;COMPLEX_CMUL;SIMPLE_COMPLEX_ARITH`a * b - b = (a - Cx(&1)) * b`]
THEN SIMP_TAC[GSYM CX_SUB;GSYM CX_MUL] THEN SUBGOAL_THEN`abs (&(dimindex (:(2,N)finite_pow)) - &1) = &(dimindex (:(2,N)finite_pow)) - &1`
ASSUME_TAC THENL[SIMP_TAC[REAL_ABS_REFL;REAL_ARITH`&0 <= a - &1 <=> &1 <= a`;REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC] THEN
SUBGOAL_THEN`~(&(dimindex (:(2,N)finite_pow)) - &1 = &0)`ASSUME_TAC THENL[SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;
REAL_ARITH`a - &1 = &0 <=> a = &1`] THEN SIMP_TAC[GSYM  REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC (REAL_ARITH`&2 <= a ==> ~(a = &1)`)
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[REAL_ARITH`&2 = &2 pow 1`] THEN MATCH_MP_TAC REAL_POW_MONO THEN
SIMP_TAC[DIMINDEX_GE_1] THEN REAL_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[REAL_FIELD`~(a = &0) ==> a * b * &1 / a = b`]
THEN ASM_SIMP_TAC[GSYM CX_ADD;COMPLEX_NORM_CX;SIN_CIRCLE] THEN REAL_ARITH_TAC;ALL_TAC] THEN
SIMP_TAC[CART_EQ;LAMBDA_BETA;D_COMPONENT] THEN SIMP_TAC[COND_LMUL] THEN REPEAT STRIP_TAC THEN AP_THM_TAC THEN AP_TERM_TAC
THEN SIMP_TAC[FINITE_NUMSEG;VSUM_CASES] THEN UNDISCH_TAC`i <= dimindex (:(2,N)finite_pow)` THEN
UNDISCH_TAC`1 <= i` THEN SIMP_TAC[GSYM IN_NUMSEG;GSYM IMP_CONJ] THEN SIMP_TAC[SET_RULE`i IN 1.. dimindex(:(2,N)finite_pow) ==>
    {j | j IN 1.. dimindex(:(2,N)finite_pow) /\ i = j} = {i}`] THEN SIMP_TAC[VSUM_SING] THEN
SIMP_TAC[SET_RULE`{i |i IN s /\ ~(k = i)} = {i | i IN s} DIFF {i |i IN s /\ i = k}`] THEN
SIMP_TAC[SET_RULE` {i |i IN s /\ i = k} SUBSET  {i | i IN s}`;SET_RULE`{i | i IN 1.. n} = (1..n)`;FINITE_NUMSEG;VSUM_DIFF]
THEN SIMP_TAC[SET_RULE`k IN 1.. n ==> {i |i IN 1..n /\ i = k } = {k}`;FINITE_NUMSEG;VSUM_CONST;VSUM_SING;CARD_NUMSEG_1] THEN
SIMP_TAC[FINITE_NUMSEG;VSUM_COMPLEX_LMUL] THEN ASM_SIMP_TAC[CVECTOR_SUB_COMPONENT;CVECTOR_ADD_COMPONENT;LAMBDA_BETA] THEN
ABBREV_TAC`x = asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))` THEN SIMP_TAC[ARITH_RULE`SUC t = t +1`] THEN
SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN SIMP_TAC[REAL_ARITH`&2 * (&t + &1) + &1 = (&2 * &t + &1) + &2`] THEN
STRIP_TAC THEN  GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV)[REAL_ADD_RDISTRIB] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV)[SIN_ADD;COS_ADD] THEN ABBREV_TAC`y = &2 * &t + &1` THEN
SIMP_TAC[FINITE_NUMSEG;VSUM_SUB] THEN SIMP_TAC[qstate_cmul] THEN ASM_SIMP_TAC[TAU_COMPONENT1;LAMBDA_BETA;TAU_PERP_COMPONENT1]
THEN SIMP_TAC[FINITE_NUMSEG;VSUM_COMPLEX_LMUL;VSUM_DELTA_ALT] THEN UNDISCH_TAC`k <= dimindex (:(2,N)finite_pow)` THEN
UNDISCH_TAC`1 <= k` THEN SIMP_TAC[GSYM IN_NUMSEG;GSYM IMP_CONJ] THEN SIMP_TAC[COMPLEX_MUL_RID] THEN
SIMP_TAC[FINITE_NUMSEG;VSUM_CASES] THEN SIMP_TAC[SET_RULE`k IN 1.. dimindex(:(2,N)finite_pow) ==>
    {i | i IN 1.. dimindex(:(2,N)finite_pow) /\ i = k} = {k}`] THEN SIMP_TAC[VSUM_SING] THEN
SIMP_TAC[SET_RULE`{i |i IN s /\ ~(i = k)} = {i | i IN s} DIFF {i |i IN s /\ i = k}`] THEN
SIMP_TAC[SET_RULE` {i |i IN s /\ i = k} SUBSET  {i | i IN s}`;SET_RULE`{i | i IN 1.. n} = (1..n)`;FINITE_NUMSEG;VSUM_DIFF]
THEN SIMP_TAC[SET_RULE`k IN 1.. n ==> {i |i IN 1..n /\ i = k } = {k}`;FINITE_NUMSEG;VSUM_CONST;VSUM_SING;CARD_NUMSEG_1]
THEN SIMP_TAC[COMPLEX_ADD_LID] THEN UNDISCH_TAC`i IN 1..dimindex (:(2,N)finite_pow)` THEN SIMP_TAC[IN_NUMSEG;LAMBDA_BETA;TAU_COMPONENT1;TAU_PERP_COMPONENT1] THEN SIMP_TAC[COND_RMUL;COND_LMUL;COMPLEX_MUL_LZERO;COMPLEX_MUL_RZERO]
THEN REPEAT STRIP_TAC THEN COND_CASES_TAC THENL[ASM_SIMP_TAC[COMPLEX_MUL_RID] THEN SIMP_TAC[SIMPLE_COMPLEX_ARITH`a * (Cx(&0) - b) = a * --b`]
THEN SIMP_TAC[GSYM CX_MUL;GSYM CX_NEG;GSYM CX_ADD;GSYM CX_SUB;COMPLEX_CMUL] THEN AP_TERM_TAC THEN SIMP_TAC[REAL_ARITH`a * b - b = (a - &1 ) * b`]
THEN ABBREV_TAC`a = sin (y * x)` THEN ABBREV_TAC`b = cos (y * x)` THEN SIMP_TAC[REAL_ARITH`(a - &1) * -- b = b - a * b`;REAL_ADD_RID]
THEN SIMP_TAC[REAL_ARITH`a - b * --c = a + b * c:real`] THEN SIMP_TAC[REAL_ARITH`a - b + c + b = a + c:real`] THEN
SIMP_TAC[REAL_ARITH`a * &1 / b = a / b`] THEN SUBGOAL_THEN`&0 <= &(dimindex (:(2,N)finite_pow)) - &1`ASSUME_TAC THENL[
SIMP_TAC[REAL_ARITH`&0 <= a - &1 <=> &1 <= a`] THEN SIMP_TAC[REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC] THEN
ASM_SIMP_TAC[REAL_DIV_SQRT] THEN SIMP_TAC[SIN_DOUBLE;COS_DOUBLE_SIN] THEN SUBGOAL_THEN`sin x = &1 / sqrt (&(dimindex (:(2,N)finite_pow)))`
SUBST1_TAC THENL[UNDISCH_TAC`asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x` THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN SIMP_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC SIN_ASN THEN STRIP_TAC THENL[SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
ASSUME_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_GE_1]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_LE]) THEN MP_TAC (REAL_ARITH`&2 <= &(2 EXP dimindex (:N)) ==> &0 < &(2 EXP dimindex (:N))`)
THEN ASM_SIMP_TAC[] THEN ONCE_SIMP_TAC[GSYM REAL_LT_INV_EQ] THEN ONCE_SIMP_TAC[GSYM SQRT_LT_0] THEN
SIMP_TAC[REAL_ARITH`&0 < a ==> -- &1 <= a`;DIMINDEX_FINITE_POW;DIMINDEX_2];ALL_TAC] THEN SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM SQRT_1] THEN SIMP_TAC[SQRT_MONO_LE_EQ] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
SIMP_TAC[REAL_ARITH`&0 < &1`] THEN SIMP_TAC[REAL_OF_NUM_CLAUSES;DIMINDEX_GE_1];ALL_TAC] THEN
SUBGOAL_THEN`cos x = sqrt(&1 - (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) pow 2)`SUBST1_TAC
THENL[UNDISCH_TAC`asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x` THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN SIMP_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC COS_ASN THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN STRIP_TAC THENL[
SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
ASSUME_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_GE_1]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_LE]) THEN MP_TAC (REAL_ARITH`&2 <= &(2 EXP dimindex (:N)) ==> &0 < &(2 EXP dimindex (:N))`)
THEN ASM_SIMP_TAC[] THEN ONCE_SIMP_TAC[GSYM REAL_LT_INV_EQ] THEN ONCE_SIMP_TAC[GSYM SQRT_LT_0] THEN
SIMP_TAC[REAL_ARITH`&0 < a ==> -- &1 <= a`];ALL_TAC] THEN SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM SQRT_1] THEN SIMP_TAC[SQRT_MONO_LE_EQ] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
SIMP_TAC[REAL_ARITH`&0 < &1`;ARITH_RULE`1 = 2 EXP 0 `;LE_EXP] THEN SIMP_TAC[ARITH_RULE`~(2 = 0)`;ARITH_RULE`~(2 = 1)`]
THEN SIMP_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC`1` THEN
SIMP_TAC[ARITH_RULE`2 EXP 0 <= 1`] THEN SIMP_TAC[GSYM DIMINDEX_2;GSYM DIMINDEX_FINITE_POW;DIMINDEX_GE_1];ALL_TAC]
THEN SUBGOAL_THEN`(&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) pow 2 = &1 / (&(dimindex (:(2,N)finite_pow)))`SUBST1_TAC
THENL[SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_INV THEN
SIMP_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC`1` THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`0 <= 1`];ALL_TAC]
THEN SIMP_TAC[REAL_SUB_LDISTRIB;REAL_ARITH`a + b - c * a = a * (&1 - c) + b`] THEN SIMP_TAC[REAL_ARITH`a * &1 - a * b + c  = a * (&1 - b) + c`]
THEN SIMP_TAC[REAL_ARITH`&2 * &1 / a = &2 / a`] THEN
AP_TERM_TAC THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2] THEN
 SUBGOAL_THEN`(&1 - inv (&(2 EXP dimindex (:N)))) = (&(2 EXP dimindex (:N)) - &1 ) / (&1 * &(2 EXP dimindex (:N)))`SUBST1_TAC
THENL[GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_SUB_INV THEN
SIMP_TAC[REAL_ARITH`~(&1 = &0)`] THEN SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
MP_TAC (SPECL[`&2`;`dimindex(:N)`]REAL_POW_LT) THEN SIMP_TAC[REAL_ARITH`&0 < &2`] THEN REAL_ARITH_TAC;ALL_TAC]
THEN SIMP_TAC[REAL_MUL_LID;real_div] THEN SIMP_TAC[SQRT_MUL;GSYM SQRT_INV] THEN SIMP_TAC[REAL_ARITH`a * b * a = (a pow 2) * b:real`]
THEN SIMP_TAC[GSYM DIMINDEX_2;GSYM DIMINDEX_FINITE_POW] THEN SIMP_TAC[DIMINDEX_2] THEN
SUBGOAL_THEN`sqrt (inv (&(dimindex (:(2,N)finite_pow)))) pow 2 = inv (&(dimindex (:(2,N)finite_pow)))`SUBST1_TAC THENL[
SIMP_TAC[SQRT_POW2] THEN MATCH_MP_TAC REAL_LE_INV THEN SIMP_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC`1`
THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`0 <= 1`];ALL_TAC] THEN REAL_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[] THEN
SIMP_TAC[COMPLEX_SUB_RZERO;COMPLEX_ADD_LID] THEN SIMP_TAC[GSYM CX_MUL;COMPLEX_CMUL;GSYM CX_SUB;GSYM CX_ADD] THEN
AP_TERM_TAC THEN ABBREV_TAC`a = sin (y * x)` THEN ABBREV_TAC`b = cos (y * x)` THEN
SIMP_TAC[REAL_ARITH`a * b - b = (a - &1) * b`] THEN SIMP_TAC[REAL_SUB_LDISTRIB]
THEN SIMP_TAC[REAL_ARITH`a * b + c - d - e * b = (a - e) * b + c - d:real`] THEN SIMP_TAC[ REAL_ARITH`a - &1 - a = -- &1`]
THEN SIMP_TAC[REAL_ARITH`a * &1 / b = a / b`] THEN SUBGOAL_THEN`&0 <= &(dimindex (:(2,N)finite_pow)) - &1`ASSUME_TAC THENL[
SIMP_TAC[REAL_ARITH`&0 <= a - &1 <=> &1 <= a`] THEN SIMP_TAC[REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC]
THEN ASM_SIMP_TAC[REAL_DIV_SQRT] THEN SIMP_TAC[SIN_DOUBLE;COS_DOUBLE_SIN] THEN SUBGOAL_THEN`sin x = &1 / sqrt (&(dimindex (:(2,N)finite_pow)))`
SUBST1_TAC THENL[UNDISCH_TAC`asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x` THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ]
THEN SIMP_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC SIN_ASN THEN STRIP_TAC THENL[SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
ASSUME_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_GE_1]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_LE]) THEN MP_TAC (REAL_ARITH`&2 <= &(2 EXP dimindex (:N)) ==> &0 < &(2 EXP dimindex (:N))`)
THEN ASM_SIMP_TAC[] THEN ONCE_SIMP_TAC[GSYM REAL_LT_INV_EQ] THEN ONCE_SIMP_TAC[GSYM SQRT_LT_0] THEN
SIMP_TAC[REAL_ARITH`&0 < a ==> -- &1 <= a`;DIMINDEX_FINITE_POW;DIMINDEX_2];ALL_TAC] THEN SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM SQRT_1] THEN SIMP_TAC[SQRT_MONO_LE_EQ] THEN
GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
SIMP_TAC[REAL_ARITH`&0 < &1`] THEN SIMP_TAC[REAL_OF_NUM_CLAUSES;DIMINDEX_GE_1];ALL_TAC] THEN
SUBGOAL_THEN`cos x = sqrt(&1 - (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) pow 2)`SUBST1_TAC
THENL[UNDISCH_TAC`asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x`
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[] THEN STRIP_TAC
THEN MATCH_MP_TAC COS_ASN THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
 THEN STRIP_TAC THENL[SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN
ASSUME_TAC (SPECL[`2`;`dimindex(:N)`]NUM_EXP_LE) THEN RULE_ASSUM_TAC(SIMP_RULE[DIMINDEX_GE_1]) THEN
RULE_ASSUM_TAC(SIMP_RULE[GSYM REAL_OF_NUM_LE]) THEN MP_TAC (REAL_ARITH`&2 <= &(2 EXP dimindex (:N)) ==> &0 < &(2 EXP dimindex (:N))`)
THEN ASM_SIMP_TAC[] THEN ONCE_SIMP_TAC[GSYM REAL_LT_INV_EQ] THEN ONCE_SIMP_TAC[GSYM SQRT_LT_0] THEN
SIMP_TAC[REAL_ARITH`&0 < a ==> -- &1 <= a`];ALL_TAC] THEN SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV]
THEN GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM SQRT_1] THEN SIMP_TAC[SQRT_MONO_LE_EQ]
THEN GEN_REWRITE_TAC(RAND_CONV o ONCE_DEPTH_CONV) [GSYM REAL_INV_1] THEN MATCH_MP_TAC REAL_LE_INV2 THEN
SIMP_TAC[REAL_ARITH`&0 < &1`;ARITH_RULE`1 = 2 EXP 0 `;LE_EXP] THEN SIMP_TAC[ARITH_RULE`~(2 = 0)`;ARITH_RULE`~(2 = 1)`]
THEN SIMP_TAC[REAL_OF_NUM_CLAUSES;DIMINDEX_GE_1] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC`1` THEN
 SIMP_TAC[ARITH_RULE`2 EXP 0 <= 1`;GSYM DIMINDEX_2;GSYM DIMINDEX_FINITE_POW;DIMINDEX_GE_1];ALL_TAC] THEN
SUBGOAL_THEN`(&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) pow 2 = &1 / (&(dimindex (:(2,N)finite_pow)))`SUBST1_TAC
THENL[SIMP_TAC[real_div;REAL_MUL_LID;GSYM SQRT_INV] THEN MATCH_MP_TAC SQRT_POW_2 THEN MATCH_MP_TAC REAL_LE_INV THEN
SIMP_TAC[REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC`1` THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`0 <= 1`];ALL_TAC]
THEN ABBREV_TAC`c = &(dimindex (:(2,N)finite_pow))` THEN SIMP_TAC[REAL_ARITH` &2 * &1 / a = &2 / a `] THEN
SIMP_TAC[REAL_ARITH` &2 * &1 / a * b = &2 / a * b`] THEN SUBGOAL_THEN`&1 - &1 / c = (c - &1) / c`SUBST1_TAC
THENL[GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[REAL_ARITH`&1 = inv (&1)`] THEN
GEN_REWRITE_TAC(LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[real_div] THEN SIMP_TAC[REAL_MUL_LID] THEN
GEN_REWRITE_TAC(RAND_CONV o RAND_CONV o ONCE_DEPTH_CONV)[REAL_ARITH`c = &1 * c`] THEN
MATCH_MP_TAC REAL_SUB_INV THEN ASM_SIMP_TAC[REAL_ARITH`&0 <= c - &1 ==> ~(c = &0)`;REAL_ARITH`~(&1 = &0)`];ALL_TAC]
THEN SIMP_TAC[SQRT_DIV] THEN SIMP_TAC[real_div;REAL_ARITH`a * (&2 * inv b) * c * inv b = &2 * a * (inv b) pow 2 * c`]
THEN SIMP_TAC[GSYM SQRT_INV] THEN SUBGOAL_THEN`sqrt (inv c) pow 2 = inv c`SUBST1_TAC THENL[SIMP_TAC[SQRT_POW2;REAL_LE_INV_EQ]
THEN ASM_SIMP_TAC[REAL_ARITH`&0 <= c - &1 ==>  &0 <= c`];ALL_TAC] THEN SIMP_TAC[REAL_SUB_RDISTRIB;REAL_SUB_LDISTRIB] THEN
SIMP_TAC[REAL_ARITH`(&2 * a * b * c) * d = &2 * a * b * (c * d)`;GSYM SQRT_MUL] THEN
SUBGOAL_THEN` sqrt ((c - &1) * inv (c - &1)) = &1`SUBST1_TAC THENL[POP_ASSUM MP_TAC THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
THEN STRIP_TAC THEN SUBGOAL_THEN`~(&(2 EXP dimindex (:N)) - &1 = &0)`ASSUME_TAC THENL[SIMP_TAC[REAL_ARITH`a - &1 = &0 <=> a = &1`]
THEN SIMP_TAC[GSYM  REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC (REAL_ARITH`&2 <= a ==> ~(a = &1)`)
THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[REAL_ARITH`&2 = &2 pow 1`] THEN MATCH_MP_TAC REAL_POW_MONO THEN
SIMP_TAC[DIMINDEX_GE_1] THEN REAL_ARITH_TAC;ALL_TAC] THEN ASM_SIMP_TAC[REAL_MUL_RINV;SQRT_EQ_1];ALL_TAC] THEN
SIMP_TAC[REAL_MUL_RID] THEN SIMP_TAC[REAL_MUL_AC] THEN SIMP_TAC[REAL_ARITH`a + b - c = d - e - c <=> a + b = d - e:real`] THEN
SUBGOAL_THEN`~(sqrt(c - &1) = &0)`ASSUME_TAC THENL[SIMP_TAC[SQRT_EQ_0] THEN SIMP_TAC[REAL_ARITH`a - &1 = &0 <=> a = &1`]
THEN POP_ASSUM MP_TAC THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
THEN SIMP_TAC[GSYM  REAL_OF_NUM_CLAUSES] THEN STRIP_TAC THEN MATCH_MP_TAC (REAL_ARITH`&2 <= a ==> ~(a = &1)`) THEN
GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[REAL_ARITH`&2 = &2 pow 1`] THEN MATCH_MP_TAC REAL_POW_MONO THEN
SIMP_TAC[DIMINDEX_GE_1] THEN REAL_ARITH_TAC;ALL_TAC] THEN
POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[REAL_ARITH `(x = y) <=> (x - y = &0)`]
THEN SIMP_TAC[REAL_ARITH`(a * -- &1 * f + b) - (c - d) = d - c - a * f + b:real`] THEN SIMP_TAC[REAL_ARITH`a - b - b + c = a - &2 * b + c`]
THEN SIMP_TAC[REAL_ARITH`a - b + c = &0 <=> c = b - a:real`] THEN STRIP_TAC THEN SIMP_TAC[REAL_ARITH`&2 * b * c - b * d * &2 * c =
(&2 * b - &2 * b * d) * c`] THEN SIMP_TAC[REAL_ARITH`&2 * b - &2 * b * c = &2 * b * (&1 - c)`] THEN SIMP_TAC[REAL_MUL_AC]
THEN AP_TERM_TAC THEN SIMP_TAC[REAL_ARITH`inv c * &2 * b = &2 * inv c * b`] THEN AP_TERM_TAC THEN
GEN_REWRITE_TAC(RAND_CONV o LAND_CONV o ONCE_DEPTH_CONV)[GSYM REAL_INV_1] THEN ASM_SIMP_TAC[REAL_ARITH`&0 <= c - &1 ==> ~(c = &0)`
;REAL_ARITH`~(&1 = &0)`;REAL_SUB_INV] THEN SIMP_TAC[real_div;REAL_MUL_LID;REAL_MUL_AC] THEN AP_TERM_TAC THEN
SUBGOAL_THEN`(c - &1) * sqrt (inv (c - &1)) = sqrt (c - &1)`SUBST1_TAC THENL[SIMP_TAC[SQRT_INV] THEN
ASM_SIMP_TAC[GSYM real_div;REAL_MUL_LID;REAL_DIV_SQRT];ALL_TAC] THEN REAL_ARITH_TAC
);;

let SET_RESTRICT = prove
(`!i k s:A -> bool.
{j | j IN s /\ j = k /\ i = k} = if i = k /\ k IN s then {k} else {}`,
REPEAT GEN_TAC THEN COND_CASES_TAC THENL[ASM SET_TAC[];ALL_TAC] THEN ASM SET_TAC[]);;

let state_after_giter = new_definition
`!k t:num. state_after_giter k t = (G k cmatrix_pow t) ** zero_h`;;

(*measure*)
let TAU_MEASUREMENT_PROB = prove
(`!t k. 1 <= k /\ k <= dimindex(:(2,N)finite_pow) ==>
    measurement (tau k:(N)qstate) (state_after_giter k t:(N)qstate)
    = sin((&2 * &t + &1) * asn(&1 / sqrt(&(dimindex(:(2,N)finite_pow))))) pow 2`,
   STRIP_TAC THEN SIMP_TAC[GROVER_ITER;measurement;state_after_giter] THEN
   ABBREV_TAC`x = (&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))`
  THEN REPEAT STRIP_TAC THEN SIMP_TAC[apply_cmatrix] THEN SUBGOAL_THEN`
  dest_qstate(mk_qstate(Cx (sin x) %%% (tau k:(N)qstate) +
  Cx (cos x) %%% (tau_perp k:(N)qstate))) = (Cx (sin x) %%% (tau k:(N)qstate) +
  Cx (cos x) %%% (tau_perp k:(N)qstate)):complex^(2,N)finite_pow`
  SUBST1_TAC THENL[MATCH_MP_TAC DEST_OF_QSTATE THEN SIMP_TAC[is_qstate;CNORM2_ALT;cdot;qstate_cmul;tau;tau_perp]
  THEN ASM_SIMP_TAC[TAU_UNIT;TAU_PERP_UNIT;DEST_OF_QSTATE] THEN SIMP_TAC[LAMBDA_BETA;CART_EQ;CVECTOR_ADD_COMPONENT]
  THEN SIMP_TAC[COND_RMUL;COMPLEX_MUL_RZERO;COMPLEX_MUL_RID] THEN SIMP_TAC[COND_RAND;COMPLEX_ADD_RID;
  COMPLEX_ADD_LID;CNJ_CX;GSYM CX_MUL] THEN SIMP_TAC[GSYM REAL_POW_2;VSUM_CASES;FINITE_NUMSEG]
  THEN UNDISCH_TAC`k <= dimindex (:(2,N)finite_pow)` THEN UNDISCH_TAC`1 <= k` THEN
  SIMP_TAC[GSYM IN_NUMSEG;GSYM IMP_CONJ] THEN SIMP_TAC[SET_RULE`k IN 1.. dimindex(:(2,N)finite_pow) ==>
    {i | i IN 1.. dimindex(:(2,N)finite_pow) /\ i = k} = {k}`] THEN SIMP_TAC[VSUM_SING] THEN
  SIMP_TAC[SET_RULE`{i |i IN s /\ ~(i = k)} = {i | i IN s} DIFF {i |i IN s /\ i = k}`] THEN
  SIMP_TAC[SET_RULE` {i |i IN s /\ i = k} SUBSET  {i | i IN s}`;SET_RULE`{i | i IN 1.. n} = (1..n)`;
  FINITE_NUMSEG;VSUM_DIFF] THEN SIMP_TAC[SET_RULE`k IN 1.. n ==> {i |i IN 1..n /\ i = k } = {k}`;
  FINITE_NUMSEG;VSUM_CONST;VSUM_SING;CARD_NUMSEG_1] THEN SIMP_TAC[REAL_POW_MUL;REAL_POW_DIV;REAL_POW_ONE;
  REAL_SQRT_POW_2;COMPLEX_CMUL;SIMPLE_COMPLEX_ARITH`a * b - b = (a - Cx(&1)) * b`]
  THEN SIMP_TAC[GSYM CX_SUB;GSYM CX_MUL] THEN SUBGOAL_THEN`abs (&(dimindex (:(2,N)finite_pow)) - &1)
  = &(dimindex (:(2,N)finite_pow)) - &1` ASSUME_TAC
  THENL[SIMP_TAC[REAL_ABS_REFL;REAL_ARITH`&0 <= a - &1 <=> &1 <= a`;REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC]
  THEN SUBGOAL_THEN`~(&(dimindex (:(2,N)finite_pow)) - &1 = &0)`ASSUME_TAC
  THENL[SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;REAL_ARITH`a - &1 = &0 <=> a = &1`] THEN
  SIMP_TAC[GSYM  REAL_OF_NUM_CLAUSES] THEN MATCH_MP_TAC (REAL_ARITH`&2 <= a ==> ~(a = &1)`)
  THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[REAL_ARITH`&2 = &2 pow 1`] THEN
  MATCH_MP_TAC REAL_POW_MONO THEN SIMP_TAC[DIMINDEX_GE_1] THEN REAL_ARITH_TAC;ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_FIELD`~(a = &0) ==> a * b * &1 / a = b`] THEN SIMP_TAC[GSYM CX_ADD;SIN_CIRCLE;COMPLEX_NORM_CX]
  THEN REAL_ARITH_TAC;ALL_TAC] THEN SIMP_TAC[CNORM2_ALT;cdot] THEN SIMP_TAC[LAMBDA_BETA;qstate_cmul] THEN ASM_SIMP_TAC[LAMBDA_BETA;TAU_COMPONENT1;TAU_PERP_COMPONENT1;CVECTOR_ADD_COMPONENT;PROJECT_TAU_COMPONENT]
  THEN SIMP_TAC[COND_LMUL;COND_RMUL;COMPLEX_MUL_RZERO;COMPLEX_MUL_RID;COMPLEX_MUL_LID;COMPLEX_MUL_LZERO]
  THEN ONCE_SIMP_TAC[COND_RAND] THEN ONCE_SIMP_TAC[COND_RATOR] THEN ONCE_SIMP_TAC[COND_RATOR] THEN
  SIMP_TAC[COMPLEX_ADD_LID;COMPLEX_ADD_RID] THEN SIMP_TAC[FINITE_NUMSEG;VSUM_CASES;VSUM_CONST;FINITE_RESTRICT]
  THEN SIMP_TAC[COMPLEX_MUL_RZERO;COMPLEX_CMUL;COMPLEX_ADD_RID] THEN SIMP_TAC[GSYM CX_ADD;GSYM CX_MUL;CNJ_CX]
  THEN SIMP_TAC[REAL_ARITH`x * x:real = x pow 2`] THEN SIMP_TAC[SET_RULE`{j | j IN {j | j IN s /\ i = j /\ i = k} /\ j = k}
  = {j | j IN s /\ i = j /\ i = k /\ j = k}`] THEN SIMP_TAC[SET_RULE`{j | j IN {j | j IN s /\ i = j /\ i = k} /\ ~(j = k)} =
  {j | j IN s /\ i = j /\ i = k /\ ~(j = k)}`] THEN SIMP_TAC[SET_RULE`{j | j IN s /\ i = j /\ i = k /\ j = k} = {j |j IN s /\ j
  = k /\ i = k}`] THEN SIMP_TAC[SET_RULE`{j | j IN s /\ i = j /\ i = k /\ ~(j = k)} = {}`;CARD_CLAUSES;
  REAL_MUL_LZERO;REAL_ADD_RID] THEN SIMP_TAC[SET_RESTRICT] THEN ASM_SIMP_TAC[IN_NUMSEG] THEN
  SIMP_TAC[COND_RAND] THEN SIMP_TAC[COND_RATOR] THEN SIMP_TAC[CARD_SING;CARD_CLAUSES;REAL_MUL_LID;REAL_MUL_LZERO]
  THEN SIMP_TAC[COND_RAND;COND_RATOR] THEN SIMP_TAC[REAL_ARITH`&0 pow 2 = &0`;VSUM_DELTA_ALT] THEN
  ASM_SIMP_TAC[IN_NUMSEG] THEN SIMP_TAC[COMPLEX_NORM_CX] THEN SIMP_TAC[REAL_LE_POW_2;REAL_ABS_REFL]
);;

let num_of_real = new_definition
 `(num_of_real:real->num) x = @n:num. &n = floor (abs(x))`;;

let NUM_OF_REAL_EXISTS = prove
(`?n. &n = floor (abs x)`,
METIS_TAC [FLOOR_POS; REAL_ABS_POS]);;

let NUM_OF_REAL = prove
(`!x. &(num_of_real x) = floor (abs(x))`,
METIS_TAC [num_of_real; NUM_OF_REAL_EXISTS;SELECT_AX]);;

let NUM_OF_REAL_EQ = prove
(`!x:real n. (n = num_of_real x) <=> (&n = floor (abs(x)))`,
ONCE_REWRITE_TAC [GSYM REAL_OF_NUM_EQ] THEN
SIMP_TAC [NUM_OF_REAL]);;

let NUM_OF_REAL_LE = prove
(`!x:real n. (n <= num_of_real x <=> &n <= floor (abs(x)))
              /\ (num_of_real x <= n <=> floor (abs(x)) <= &n)`,
SIMP_TAC [GSYM REAL_OF_NUM_LE; NUM_OF_REAL]);;

let NUM_OF_REAL_LT = prove
(`!x:real n. (n < num_of_real x <=> &n < floor (abs(x)))
              /\ (num_of_real x < n <=> floor (abs(x)) < &n)`,
SIMP_TAC [GSYM REAL_OF_NUM_LT; NUM_OF_REAL]);;

let NUM_OF_REAL_ADD = prove
(`!x:real n. &(num_of_real x + n) = floor(abs(x)) + &n`,
SIMP_TAC [GSYM REAL_OF_NUM_ADD; NUM_OF_REAL]);;

let ADD_SIN = prove
 (`!x y. sin(x) + sin(y) = &2 * sin((x + y) / &2) * cos((x - y) / &2)`,
 REPEAT GEN_TAC THEN SUBGOAL_THEN`sin x = sin ((x +y) / &2 + (x-y) / &2)`SUBST1_TAC THENL[SIMP_TAC[REAL_ARITH`(x + y) / &2 + (x - y) / &2 = x`];
 ALL_TAC] THEN SUBGOAL_THEN`sin y = sin ((x +y) / &2 - (x-y) / &2)`SUBST1_TAC THENL[SIMP_TAC[REAL_ARITH`(x + y) / &2 - (x - y) / &2 = y`];
 ALL_TAC] THEN SIMP_TAC[SIN_ADD;SIN_SUB] THEN SIMP_TAC[REAL_ARITH`(a + b) + a - b = &2 * a:real`]);;

let SUB_SIN = prove
(`!x y. sin(x) - sin(y) = &2 * sin((x - y) / &2) * cos((x + y) / &2)`,
REPEAT GEN_TAC THEN SUBGOAL_THEN`sin x = sin ((x +y) / &2 + (x-y) / &2)`SUBST1_TAC THENL[SIMP_TAC[REAL_ARITH`(x + y) / &2 + (x - y) / &2 = x`];
 ALL_TAC] THEN SUBGOAL_THEN`sin y = sin ((x +y) / &2 - (x-y) / &2)`SUBST1_TAC THENL[SIMP_TAC[REAL_ARITH`(x + y) / &2 - (x - y) / &2 = y`];
 ALL_TAC] THEN SIMP_TAC[SIN_ADD;SIN_SUB] THEN SIMP_TAC[REAL_ARITH`(a + b) - (a - b) = &2 * b:real`;REAL_ARITH`a * b  = b * a:real`]
);;

let SIN_POW2_SUB = prove
 (`!x y. sin(x) pow 2 - sin(y) pow 2 = sin(x + y) * sin(x - y)`,
  REPEAT GEN_TAC THEN SIMP_TAC[ REAL_ARITH`(a:real) pow 2 - b pow 2 = (a+b) * (a-b)`;ADD_SIN;SUB_SIN]
  THEN SIMP_TAC[REAL_ARITH`(&2 * a * b) * &2 *(c * d) = (&2 * a * d) * &2 * c * b`;GSYM SIN_DOUBLE]
  THEN SIMP_TAC[REAL_ARITH`&2 * a / &2 = a`]);;

let SIN_POS_LE_PI2 = prove
 (`!x. &0 < x /\ x <= pi / &2 ==> &0 < sin(x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
  ASM_REAL_ARITH_TAC);;

let SIN_POW2_PERIODIC = prove
(`!x. sin(x + pi) pow 2 = sin(x) pow 2`,
ONCE_SIMP_TAC[REAL_ARITH`a = b <=> a - b = &0`] THEN SIMP_TAC[SIN_POW2_SUB]
THEN SIMP_TAC[REAL_ARITH`(a + b) - a = b:real`;SIN_PI;REAL_MUL_RZERO]
);;

let SIN_POW2_NPI = prove
(`!x n.sin (x) pow 2 = sin (x + &n * pi) pow 2`,
REPEAT GEN_TAC THEN ONCE_SIMP_TAC[REAL_ARITH`a = b <=> a - b = &0`] THEN SIMP_TAC[SIN_POW2_SUB]
THEN SIMP_TAC[REAL_ARITH`x - (x + y) = -- y:real`] THEN SIMP_TAC[SIN_NEG;SIN_NPI] THEN
REAL_ARITH_TAC
);;

let SIN_POW2_MOD_PI = prove
(`!x.sin (x) pow 2 = sin (x - pi * floor (x / pi)) pow 2`,
GEN_TAC THEN ONCE_SIMP_TAC[REAL_ARITH`a = b <=> a - b = &0`] THEN SIMP_TAC[SIN_POW2_SUB]
THEN SIMP_TAC[REAL_ARITH`x - (x - y) = y:real`] THEN SUBGOAL_THEN`sin (pi * floor (x / pi)) = &0`SUBST1_TAC
THENL[SIMP_TAC[SIN_EQ_0] THEN EXISTS_TAC`floor(x / pi)` THEN SIMP_TAC[FLOOR;REAL_MUL_SYM];ALL_TAC]
THEN REAL_ARITH_TAC
);;

let SIN_TREBLE_SIN = prove
 (`!x. sin(&3 * x) = &3 * sin x - &4 * sin(x) pow 3 `,
 GEN_TAC THEN MP_TAC(SPEC`pi / &2 - x`COS_TREBLE_COS) THEN
 SIMP_TAC[REAL_SUB_LDISTRIB;GSYM SIN_COS;COS_SUB;COS_NEG;SIN_NEG]
 THEN SIMP_TAC[REAL_ARITH`&3 * a / &2 = a / &2 + a`;SIN_PERIODIC_PI;COS_PERIODIC_PI]
 THEN SIMP_TAC[SIN_PI2;COS_PI2;COS_TREBLE_COS] THEN REAL_ARITH_TAC
 );;

let SIN_PI10 = prove
(`sin(pi / &10) = (sqrt (&5) - &1) / &4`,
  MP_TAC(SPEC`pi / &10`SIN_TREBLE_SIN) THEN GEN_REWRITE_TAC(LAND_CONV o LAND_CONV o
  ONCE_DEPTH_CONV)[SIN_COS] THEN SIMP_TAC[REAL_ARITH`a / &2 - &3 * a / &10 = &2 * a / &10`]
  THEN SIMP_TAC[COS_DOUBLE_SIN] THEN ABBREV_TAC `x = sin(pi / &10)` THEN SIMP_TAC[REAL_RING
  `&1 - &2 * x pow 2 = &3 * x - &4 * x pow 3 <=> x = &1 \/ &4 * x pow 2 + &2 * x - &1 = &0`]
  THEN STRIP_TAC THENL[SUBGOAL_THEN`~(x = &1)`ASSUME_TAC THENL[UNDISCH_TAC`sin (pi / &10) = x`
  THEN ONCE_SIMP_TAC[EQ_SYM_EQ] THEN STRIP_TAC THEN REWRITE_TAC[GSYM SIN_PI2] THEN
  MATCH_MP_TAC (REAL_ARITH`a < b ==> ~(a = b:real)`) THEN MATCH_MP_TAC SIN_MONO_LT THEN
  SIMP_TAC[PI_POS_LE;REAL_ARITH`&0 <= a ==> --(a / &2) <= a / &10`] THEN SIMP_TAC[PI_POS;
  REAL_ARITH`&0 < a ==> a / &10 < a / &2`] THEN REAL_ARITH_TAC;ALL_TAC] THEN ASM_REAL_ARITH_TAC
  ;ALL_TAC] THEN SUBGOAL_THEN`&0 < x`ASSUME_TAC THENL[UNDISCH_TAC`sin (pi / &10) = x`
  THEN ONCE_SIMP_TAC[EQ_SYM_EQ] THEN STRIP_TAC THEN MATCH_MP_TAC SIN_POS_LE_PI2 THEN
  SIMP_TAC[REAL_ARITH`&0 < a ==> &0 < a / &10 /\ a / &10 <= a / &2`;PI_POS];ALL_TAC] THEN
  UNDISCH_TAC`&4 * x pow 2 + &2 * x - &1 = &0` THEN SIMP_TAC[REAL_ARITH`&4 * x pow 2 + &2 * x - &1
  = &0 <=> (&2 * x) pow 2 + &2 * x + (&1 / &2) pow 2 = &5 / &4`] THEN SIMP_TAC[REAL_ARITH`a pow 2 +
  a + (&1 / &2) pow 2 = (a + &1 / &2) pow 2`] THEN SUBGOAL_THEN`&5 / &4 = (sqrt(&5) / &2) pow 2`SUBST1_TAC
  THENL[SIMP_TAC[REAL_POW_DIV;REAL_ARITH`&2 pow 2 = &4`] THEN SIMP_TAC[SQRT_POW_2;REAL_ARITH`&0 <= &5`]
  ;ALL_TAC] THEN SIMP_TAC[GSYM REAL_EQ_SQUARE_ABS] THEN SUBGOAL_THEN`abs (&2 * x + &1 / &2) = &2 * x + &1 / &2`
  SUBST1_TAC THENL[SIMP_TAC[REAL_ABS_REFL] THEN ASM_REAL_ARITH_TAC;ALL_TAC] THEN
  SUBGOAL_THEN`abs(sqrt (&5) / &2) = sqrt (&5) / &2`SUBST1_TAC THENL[SIMP_TAC[REAL_ABS_REFL] THEN
  SIMP_TAC[REAL_ARITH`&0 <= a / &2 <=> &0 <= a`] THEN SIMP_TAC[SQRT_LE_0] THEN REAL_ARITH_TAC;ALL_TAC]
  THEN REAL_ARITH_TAC
);;

let OPT_GROVER_STEPS = prove
(`!k t' :num.
  1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\ (&2 * &t' + &1) * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) <= pi ==>
  measurement (tau k:(N)qstate) (state_after_giter k t':(N)qstate) <=
   measurement (tau k:(N)qstate) (state_after_giter k (
   num_of_real ((pi / (&4 *  asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) - &1 / &2)):(N)qstate) \/
   measurement (tau k:(N)qstate) (state_after_giter k t':(N)qstate) <=
   measurement (tau k:(N)qstate) (state_after_giter k (
   num_of_real ((pi / (&4 *  asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))))) - &1 / &2) + 1):(N)qstate)`,
   SIMP_TAC[TAU_MEASUREMENT_PROB] THEN REPEAT STRIP_TAC THEN ABBREV_TAC`x = asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))`
   THEN SIMP_TAC[NUM_OF_REAL;NUM_OF_REAL_ADD] THEN
   SUBGOAL_THEN`abs (pi / (&4 * x) - &1 / &2) = pi / (&4 * x) - &1 / &2`SUBST1_TAC THENL[
   SIMP_TAC[REAL_ABS_REFL;REAL_ARITH`&0 <= b - c <=> c <= b`] THEN SIMP_TAC[REAL_FIELD`&1 / &2 <=
   pi / (&4 * x) <=> &2  <= pi / x`] THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RCANCEL_IMP
   THEN EXISTS_TAC`x:real` THEN SUBGOAL_THEN`&0 < x`ASSUME_TAC THENL[POP_ASSUM MP_TAC THEN ONCE_SIMP_TAC[EQ_SYM_EQ]
   THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ASN_0] THEN MATCH_MP_TAC ASN_MONO_LT THEN SIMP_TAC[REAL_ARITH`-- &1 <= &0`]
   THEN ONCE_REWRITE_TAC[GSYM SQRT_1] THEN SIMP_TAC[GSYM SQRT_DIV] THEN STRIP_TAC THENL[MATCH_MP_TAC SQRT_POS_LT THEN
   SIMP_TAC[real_div;REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_INV THEN SIMP_TAC[REAL_OF_NUM_LT] THEN
   MATCH_MP_TAC (ARITH_RULE`1 <= a ==> 0 < a`) THEN SIMP_TAC[DIMINDEX_GE_1];ALL_TAC] THEN MATCH_MP_TAC SQRT_MONO_LE
   THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN SIMP_TAC[DIMINDEX_GE_1;REAL_OF_NUM_LE];ALL_TAC]
   THEN ASM_SIMP_TAC[REAL_MUL_AC;REAL_FIELD`&0 < x ==> inv x * x = &1`;REAL_MUL_RID] THEN SIMP_TAC[REAL_FIELD`a * &2 <= pi
   <=> a <= pi / &2`] THEN SIMP_TAC[GSYM ASN_1] THEN UNDISCH_TAC`asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x`
   THEN ONCE_SIMP_TAC[EQ_SYM_EQ] THEN STRIP_TAC THEN MATCH_MP_TAC ASN_MONO_LE THEN SIMP_TAC[real_div;REAL_MUL_LID;
   REAL_ARITH`&1 <= &1`] THEN STRIP_TAC THENL[SIMP_TAC[GSYM SQRT_INV] THEN
   MATCH_MP_TAC (REAL_ARITH`&0 <= a ==> -- &1 <= a`) THEN ONCE_REWRITE_TAC[GSYM SQRT_0] THEN MATCH_MP_TAC
   SQRT_MONO_LE THEN MATCH_MP_TAC REAL_LE_INV THEN SIMP_TAC[REAL_OF_NUM_LE;REAL_OF_NUM_LT] THEN
   SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= a ==> 0 <= a`];ALL_TAC] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
   MATCH_MP_TAC REAL_LE_RSQRT THEN SIMP_TAC[REAL_POW_ONE] THEN SIMP_TAC[DIMINDEX_GE_1;REAL_OF_NUM_LE];ALL_TAC]
   THEN ABBREV_TAC`t = floor (pi / (&4 * x) - &1 / &2)` THEN ASM_CASES_TAC`&t' <= t` THENL[DISJ1_TAC THEN
   MP_TAC (CONJUNCT2(SPEC `pi / (&4 * x) - &1 / &2` FLOOR)) THEN ASM_SIMP_TAC[] THEN SIMP_TAC [GSYM REAL_LE_SQUARE_ABS]
   THEN SIMP_TAC[REAL_ARITH`a - &1 / &2 < t + &1 <=> a - &3 / &2 < t`] THEN REWRITE_TAC[REAL_ARITH`a - &3 / &2 < t
   <=> &2 * a - &2 < &2 * t + &1`] THEN REWRITE_TAC[ REAL_ARITH`t <= a - &1 / &2 <=> &2 * t + &1 <= &2 * a`]
   THEN RULE_ASSUM_TAC(ONCE_SIMP_RULE[REAL_ARITH`a <= b <=> &2 * a + &1 <= &2 * b + &1`]) THEN
   POP_ASSUM MP_TAC THEN ABBREV_TAC`a = &2 * &t' + &1` THEN ABBREV_TAC`b = &2 * t + &1` THEN
   STRIP_TAC THEN SUBGOAL_THEN`&0 <= x /\ x <= pi / &2`ASSUME_TAC THENL[
   UNDISCH_TAC`asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x` THEN ONCE_SIMP_TAC[EQ_SYM_EQ] THEN STRIP_TAC
   THEN MATCH_MP_TAC ASN_BOUNDS_PI2 THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN STRIP_TAC THENL[SIMP_TAC[REAL_LE_INV_EQ]
   THEN SIMP_TAC[SQRT_LE_0] THEN SIMP_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC (SPECL[`0`;`1`;`dimindex (:(2,N)finite_pow)`]
   LE_TRANS) THEN SIMP_TAC[DIMINDEX_GE_1] THEN ARITH_TAC;ALL_TAC] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
   ONCE_REWRITE_TAC[GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN SIMP_TAC[REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC]
   THEN SIMP_TAC[REAL_FIELD`&2 * pi / (&4 * x) = pi / (&2 * x)`] THEN SUBGOAL_THEN`~(x = &0)`ASSUME_TAC THENL[UNDISCH_TAC`
   asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x` THEN ONCE_SIMP_TAC[EQ_SYM_EQ] THEN STRIP_TAC THEN MATCH_MP_TAC
   REAL_LT_IMP_NZ THEN ONCE_REWRITE_TAC[GSYM ASN_0] THEN MATCH_MP_TAC ASN_MONO_LT THEN SIMP_TAC[REAL_ARITH`-- &1 <= &0`]
   THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN SIMP_TAC[REAL_LT_INV_EQ] THEN SIMP_TAC[SQRT_LT_0] THEN STRIP_TAC THENL[
   SIMP_TAC[REAL_OF_NUM_LT] THEN MATCH_MP_TAC (ARITH_RULE`1 <= a ==> 0 < a`) THEN SIMP_TAC[DIMINDEX_GE_1];ALL_TAC] THEN
   MATCH_MP_TAC REAL_INV_LE_1 THEN ONCE_REWRITE_TAC[GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
   SIMP_TAC[REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC] THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN SIMP_TAC[REAL_INV_MUL]
   THEN STRIP_TAC THEN SUBGOAL_THEN`b * x <= pi * inv (&2) /\ pi * inv (&2) - &2 * x < b * x`ASSUME_TAC THENL[
   UNDISCH_TAC`&0 <= x /\ x <= pi / &2` THEN REPEAT STRIP_TAC THENL[MP_TAC (SPECL[`b:real`;`pi * inv(&2) * inv (x)`;
   ` x:real`] REAL_LE_RMUL) THEN ASM_SIMP_TAC[REAL_ARITH`(a * b * c) * d = a * b * c * d:real`;REAL_MUL_LINV]
   THEN SIMP_TAC[REAL_MUL_RID];ALL_TAC] THEN MP_TAC (SPECL[`pi * inv(&2) * inv (x) - &2`;`b:real`;` x:real`] REAL_LT_RMUL)
   THEN ASM_SIMP_TAC[REAL_ARITH`~(x = &0) /\ &0 <= x ==> &0 < x`] THEN SIMP_TAC[REAL_SUB_RDISTRIB] THEN ASM_SIMP_TAC[
   REAL_ARITH`(a * b * c) * d = a * b * c * d:real`;REAL_MUL_LINV;REAL_MUL_RID];ALL_TAC] THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC[GSYM real_div] THEN MP_TAC (REAL_ARITH`&0 <= x /\ x <= pi / &2 <=> &0 <= &2 * x /\ &2 * x <= pi`) THEN
   ASM_SIMP_TAC[] THEN SIMP_TAC[REAL_ARITH`&2 * x <= pi <=> -- pi / &2 <= pi / &2 - &2 * x`] THEN SIMP_TAC[
   REAL_ARITH`&0 <= &2 * x <=> pi / &2 - &2 * x <= pi / &2`] THEN REPEAT STRIP_TAC THEN MP_TAC (REAL_ARITH`
   pi / &2 - &2 * x <= pi / &2 /\ -- pi / &2 <= pi / &2 - &2 * x /\ b * x <= pi / &2 /\ pi / &2 - &2 * x < b * x ==>
   -- pi / &2 <= b * x /\ b * x <= pi / &2`) THEN ASM_SIMP_TAC[] THEN SUBGOAL_THEN`&1 <= a`ASSUME_TAC THENL[
   UNDISCH_TAC`&2 * &t' + &1 = a` THEN ONCE_SIMP_TAC[EQ_SYM_EQ] THEN STRIP_TAC THEN SIMP_TAC[REAL_ARITH`&1 <= a + &1
   <=> &0 <= a`] THEN SIMP_TAC[REAL_OF_NUM_CLAUSES] THEN ARITH_TAC;ALL_TAC] THEN MP_TAC (REAL_ARITH`&1 <= a /\ a <= b
   ==> &0 <= b`) THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN MP_TAC (SPECL[`b:real`;`x:real`] REAL_LE_MUL) THEN
   ASM_SIMP_TAC[] THEN MP_TAC (SPECL[`a:real`;`x:real`] REAL_LE_MUL) THEN ASM_SIMP_TAC[REAL_ARITH`&1 <= a ==> &0 <= a`]
   THEN REPEAT STRIP_TAC THEN MP_TAC (SPECL[`a:real`;`b:real`;`x:real`] REAL_LE_RMUL) THEN ASM_SIMP_TAC[] THEN
   REPEAT STRIP_TAC THEN MP_TAC (REAL_ARITH`a * x <= b * x /\ b * x <= pi / &2 ==> a * x <= pi / &2`) THEN
   ASM_SIMP_TAC[] THEN MP_TAC (REAL_ARITH`&1 <= a ==> &0 <= a`) THEN ASM_SIMP_TAC[] THEN REPEAT STRIP_TAC THEN
   MATCH_MP_TAC (REAL_ARITH`&0 <= a /\ a <= b ==> abs a <= abs b`) THEN STRIP_TAC THENL[SIMP_TAC[REAL_ARITH`&0 <= a
   <=> a = &0 \/ &0 < a`] THEN DISJ2_TAC THEN MATCH_MP_TAC SIN_POS_LE_PI2 THEN SIMP_TAC[REAL_ARITH`&0 < a * x <=>
   (&0 <= a * x /\ ~(a * x = &0))`] THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN MATCH_MP_TAC REAL_LT_MUL
   THEN ASM_SIMP_TAC[REAL_ARITH `&0 < x <=> &0 <= x /\ ~(x = &0)`] THEN ASM_SIMP_TAC[REAL_ARITH`&1 <= a ==> ~(a = &0)`]
   ;ALL_TAC] THEN MATCH_MP_TAC SIN_MONO_LE THEN ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC`&0`
   THEN ASM_REAL_ARITH_TAC;ALL_TAC] THEN POP_ASSUM MP_TAC THEN REWRITE_TAC[REAL_ARITH`~(&t' <= t) <=> t < &t'`] THEN
   GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[GSYM FLOOR_NUM] THEN STRIP_TAC THEN
   MP_TAC(SPECL[`&t'`;`t:real`]REAL_LT_FLOOR) THEN STRIP_TAC THEN UNDISCH_TAC`floor (pi / (&4 * x) - &1 / &2) = t`
   THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)[EQ_SYM_EQ] THEN STRIP_TAC THEN
   UNDISCH_TAC`integer t ==> (t < floor (&t') <=> t <= &t' - &1)` THEN ASM_SIMP_TAC[CONJUNCT1 (SPEC `t:real`FLOOR)]
   THEN STRIP_TAC THEN UNDISCH_TAC`t = floor (pi / (&4 * x) - &1 / &2)` THEN GEN_REWRITE_TAC(LAND_CONV o ONCE_DEPTH_CONV)
   [EQ_SYM_EQ] THEN STRIP_TAC THEN UNDISCH_TAC`floor (pi / (&4 * x) - &1 / &2) <= &t' - &1` THEN ASM_SIMP_TAC[] THEN
   SIMP_TAC [GSYM REAL_LE_SQUARE_ABS] THEN SIMP_TAC[REAL_ARITH`&2 * (t + &1) + &1 = &2 * t + &3`] THEN
   STRIP_TAC THEN MP_TAC (CONJUNCT2(SPEC `pi / (&4 * x) - &1 / &2` FLOOR)) THEN ASM_SIMP_TAC[] THEN STRIP_TAC
   THEN DISJ2_TAC THEN POP_ASSUM MP_TAC THEN SIMP_TAC[REAL_ARITH`a - &1 / &2 < t + &1 <=> &2 * a < &2 * t + &3`]
   THEN RULE_ASSUM_TAC(ONCE_SIMP_RULE[REAL_ARITH`a <= b - &1 <=> &2 * a + &3 <= &2 * b + &1`]) THEN
   ABBREV_TAC`a = &2 * &t' + &1` THEN ABBREV_TAC`b = &2 * t + &3` THEN SUBGOAL_THEN`&0 <= x /\ x <= pi / &2`ASSUME_TAC
   THENL[UNDISCH_TAC`asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x` THEN ONCE_SIMP_TAC[EQ_SYM_EQ] THEN STRIP_TAC
   THEN MATCH_MP_TAC ASN_BOUNDS_PI2 THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN STRIP_TAC THENL[SIMP_TAC[REAL_LE_INV_EQ]
   THEN SIMP_TAC[SQRT_LE_0] THEN SIMP_TAC[REAL_OF_NUM_LE] THEN MATCH_MP_TAC (SPECL[`0`;`1`;`dimindex (:(2,N)finite_pow)`]
   LE_TRANS) THEN SIMP_TAC[DIMINDEX_GE_1] THEN ARITH_TAC;ALL_TAC] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
   ONCE_REWRITE_TAC[GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN SIMP_TAC[REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC]
   THEN SIMP_TAC[REAL_FIELD`&2 * pi / (&4 * x) = pi / (&2 * x)`] THEN SUBGOAL_THEN`~(x = &0)`ASSUME_TAC THENL[UNDISCH_TAC`
   asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow)))) = x` THEN ONCE_SIMP_TAC[EQ_SYM_EQ] THEN STRIP_TAC THEN MATCH_MP_TAC
   REAL_LT_IMP_NZ THEN ONCE_REWRITE_TAC[GSYM ASN_0] THEN MATCH_MP_TAC ASN_MONO_LT THEN SIMP_TAC[REAL_ARITH`-- &1 <= &0`]
   THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN SIMP_TAC[REAL_LT_INV_EQ] THEN SIMP_TAC[SQRT_LT_0] THEN STRIP_TAC THENL[
   SIMP_TAC[REAL_OF_NUM_LT] THEN MATCH_MP_TAC (ARITH_RULE`1 <= a ==> 0 < a`) THEN SIMP_TAC[DIMINDEX_GE_1];ALL_TAC] THEN
   MATCH_MP_TAC REAL_INV_LE_1 THEN ONCE_REWRITE_TAC[GSYM SQRT_1] THEN MATCH_MP_TAC SQRT_MONO_LE THEN
   SIMP_TAC[REAL_OF_NUM_LE;DIMINDEX_GE_1];ALL_TAC] THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN SIMP_TAC[REAL_INV_MUL]
   THEN STRIP_TAC THEN SUBGOAL_THEN`pi * inv (&2) < b * x`ASSUME_TAC THENL[MP_TAC(SPECL[`pi * inv(&2) * inv x`;`b:real`;
   `x:real`]REAL_LT_RMUL) THEN ASM_SIMP_TAC[REAL_ARITH`(a * b * c) * d = a * b * c * d:real`;REAL_MUL_LINV] THEN
   ASM_SIMP_TAC[REAL_MUL_RID;REAL_ARITH`&0 < x <=> &0 <= x /\ ~(x = &0)`];ALL_TAC] THEN MP_TAC(SPECL[`b:real`;`a:real`;
   `x:real`] REAL_LE_RMUL) THEN ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM real_div] THEN REPEAT STRIP_TAC
   THEN MATCH_MP_TAC (REAL_ARITH`&0 <= a /\ a <= b ==> abs a <= abs b`) THEN STRIP_TAC THENL[MATCH_MP_TAC SIN_POS_PI_LE
   THEN MP_TAC(REAL_ARITH`pi / &2 < b * x /\ b * x <= a * x ==> pi / &2 <= a * x`) THEN ASM_SIMP_TAC[] THEN
   SIMP_TAC[REAL_ARITH`&0 < pi / &2 /\ pi / &2 <= a ==> &0 <= a`;PI2_BOUNDS];ALL_TAC] THEN SIMP_TAC[SIN_COS]
   THEN ONCE_SIMP_TAC[REAL_ARITH`a - b = --(b - a:real)`] THEN SIMP_TAC[COS_NEG] THEN MATCH_MP_TAC COS_MONO_LE
   THEN ASM_SIMP_TAC[REAL_ARITH`a - b <= c - b <=> a <= c:real`] THEN SIMP_TAC[REAL_ARITH`&0 <= a - b <=> b <= a`]
   THEN ASM_SIMP_TAC[REAL_ARITH`a < b ==> a <= b:real`] THEN ASM_REAL_ARITH_TAC
);;

(*Geometric induction*)

let zero_h_alt = new_definition
`(zero_h_alt:real -> real^2) x = vector[(cos x);(sin x)]`;;


let grotate = new_definition
`grotate (x:real):real^2^2 = vector[vector[cos(&2 * x); --sin(&2 * x)];
                                   vector[sin(&2 * x); cos(&2 * x)]]`;;

make_overloadable "matrix_pow" `:A^N^N->num->A^N^N`;;

overload_interface("matrix_pow",`real_matrix_pow:real^N^N->num->real^N^N`);;

let real_matrix_pow = define
    `((real_matrix_pow: real^N^N->num->real^N^N) A 0 = (mat 1:real^N^N)) /\ (real_matrix_pow A (SUC n) = A ** (real_matrix_pow A n))`;;

let matrix_pow = prove
    (`(!A. (real_matrix_pow A 0 = (mat 1:real^N^N)) /\ (real_matrix_pow A (SUC n) = A ** (real_matrix_pow A n)))`,
    SIMP_TAC[real_matrix_pow]);;

parse_as_infix("matrix_pow",(200,"right"));;

let MATRIX_POW_1 = prove
    (`!A:real^N^N. A matrix_pow 1 = A`,
     REWRITE_TAC[num_CONV `1`] THEN SIMP_TAC[matrix_pow;MATRIX_MUL_RID]);;

let MATRIX_POW_2 =  prove
    (`!A:real^N^N. A matrix_pow 2 = A ** A`,
    SIMP_TAC[matrix_pow;num_CONV `2`;MATRIX_POW_1]);;

let MATRIX_POW_3 =  prove
    (`!A:real^N^N. A matrix_pow 3 = A ** A ** A`,
    SIMP_TAC[matrix_pow;num_CONV `3`;num_CONV `2`;MATRIX_POW_1]);;

let MATRIX_POW_0 = prove
    (`!n. (mat 0:real^N^N) matrix_pow SUC n = (mat 0:real^N^N)`,
     SIMP_TAC[matrix_pow;MATRIX_MUL_LZERO]);;

let MATRIX_POW_ONE = prove
    (`!n. (mat 1:real^N^N) matrix_pow n = (mat 1:real^N^N)`,
     INDUCT_TAC THEN ASM_SIMP_TAC [matrix_pow;MATRIX_MUL_LID]);;

let MATRIX_POW_ADD = prove
    (`!A:real^N^N m n. A matrix_pow (m + n) = (A matrix_pow m) ** (A matrix_pow n)`,
     GEN_TAC THEN INDUCT_TAC THEN
     ASM_REWRITE_TAC[matrix_pow; ADD_CLAUSES; MATRIX_MUL_LID] THEN REWRITE_TAC[MATRIX_MUL_ASSOC]);;

let MATRIX_POW_CMUL = prove
    (`!k:real A:real^N^N n:num. (k %% A) matrix_pow n = (k pow n) %% (A matrix_pow n)`,
     GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
     [SIMP_TAC [matrix_pow; real_pow; GSYM MAT_CMUL;ARITH];
      SIMP_TAC [matrix_pow;real_pow] THEN
      ASM_SIMP_TAC [MATRIX_MUL_LMUL;MATRIX_MUL_RMUL;MATRIX_CMUL_ASSOC]]);;

let MATRIX_POW_TRANSP = prove
    (`!A:real^N^N n:num. (transp A) matrix_pow n  = transp(A matrix_pow n)`,
    let MATRIX_POW_SUC = prove
    ( `!A:real^N^N n:num.A matrix_pow n ** A = A ** A matrix_pow n`,
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[matrix_pow;MATRIX_MUL_RID;MATRIX_MUL_LID]
    THEN SIMP_TAC[matrix_pow] THEN FIRST_ASSUM (SUBST1_TAC o SYM) THEN
    SIMP_TAC[MATRIX_MUL_ASSOC] THEN FIRST_ASSUM (SUBST1_TAC o SYM)
    THEN SIMP_TAC[])  in
    GEN_TAC THEN INDUCT_TAC THEN SIMP_TAC[matrix_pow;TRANSP_MAT] THEN
    ASM_SIMP_TAC[matrix_pow;GSYM MATRIX_TRANSP_MUL;MATRIX_POW_SUC]);;


let GROVERR_ROTATION = prove
(`!n:num.(grotate(x:real) matrix_pow n) ** zero_h_alt(x:real) = vector[cos((&2 * &n + &1) * x);sin((&2 * &n + &1) * x)]`,
SIMP_TAC[zero_h_alt] THEN INDUCT_TAC THENL[SIMP_TAC[REAL_ARITH`&2 * &0 = &0`;REAL_ARITH`&0 + &1 = &1`; REAL_ARITH`&1 * x = x`]
THEN SIMP_TAC[matrix_pow;matrix_vector_mul] THEN SIMP_TAC[CART_EQ;LAMBDA_BETA;MAT_COMPONENT]
THEN SIMP_TAC[COND_LMUL;REAL_ARITH`&1 * a = a`;REAL_ARITH`&0 * a = &0`;DIMINDEX_2] THEN
REWRITE_TAC[num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN REWRITE_TAC[SUM_SING_NUMSEG; ARITH; REAL_ADD_ASSOC]
THEN SIMP_TAC[VECTOR_1;VECTOR_2;FORALL_2] THEN SIMP_TAC[ARITH_RULE`1=2 <=> F`;ARITH_RULE`2=1 <=> F`;
REAL_ARITH`a + &0 = a /\ &0 + a = a`];ALL_TAC] THEN SIMP_TAC[ARITH_RULE`SUC n = 1 + n`;
MATRIX_POW_ADD;MATRIX_POW_1] THEN ASM_SIMP_TAC[GSYM MATRIX_VECTOR_MUL_ASSOC] THEN
SIMP_TAC[grotate;matrix_vector_mul;DIMINDEX_2] THEN SIMP_TAC[LAMBDA_BETA;CART_EQ] THEN
REWRITE_TAC[num_CONV `2`; SUM_CLAUSES_NUMSEG] THEN REWRITE_TAC[SUM_SING_NUMSEG;ARITH;REAL_ADD_ASSOC]
THEN SIMP_TAC[DIMINDEX_2;VECTOR_1;VECTOR_2;FORALL_2;REAL_ARITH`(a:real) + --b * c = a - b * c `] THEN
SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES;REAL_ARITH`(&2 * (&1 + &n) + &1) * x =
&2 * x + ((&2 * &n + &1) * x)`;SIN_ADD;COS_ADD]
);;

let SIN_POW2_INCRE = prove
(`!n:num x:real. &0 < x /\ x < pi / &2
    /\ &n < pi / (&4 * x) - & 1 ==>
    &0 < sin((&2 * &n + &3) * x) pow 2 - sin((&2 * &n + &1) * x) pow 2`,
    REPEAT STRIP_TAC THEN SIMP_TAC[SIN_POW2_SUB;REAL_ARITH`a * x + b * x = (a + b) * x:real`;
    REAL_ARITH`a * x - b * x = (a - b) * x:real`;REAL_ARITH`(&2 * a + &3) + &2 * a + &1  = &4 * a + &4`;
    REAL_ARITH`(&2 * a + &3) - (&2 * a + &1)  = &2`] THEN MATCH_MP_TAC REAL_LT_MUL THEN
    STRIP_TAC THENL[MATCH_MP_TAC SIN_POS_PI THEN SIMP_TAC[REAL_ARITH`&4 * &n + &4 = &4 * (&n + &1)`]
    THEN SIMP_TAC[REAL_ARITH`&0 < (&4 * (&n + &1)) * x <=> &0 < (&n + &1) * x`] THEN STRIP_TAC
    THENL[ASM_SIMP_TAC[REAL_OF_NUM_SUC;REAL_OF_NUM_LT;REAL_LT_MUL;LT_0];ALL_TAC] THEN
    POP_ASSUM MP_TAC THEN SIMP_TAC[REAL_ARITH`&n < a - &1 <=> &n + &1 < a`] THEN
    RULE_ASSUM_TAC(ONCE_SIMP_RULE[REAL_ARITH`&0 < x <=> &0 < &4 * x`]) THEN
    SIMP_TAC[REAL_ARITH`(&4 * a) * x = a * (&4 * x) `]
    THEN STRIP_TAC THEN MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC`&1 / (&4 * x)`
    THEN ASM_SIMP_TAC[REAL_FIELD`&0 < b ==> (a * b ) * &1 / b = a`] THEN
    ASM_SIMP_TAC[REAL_ARITH`&0 < x ==> &1 / x = inv x`;REAL_LT_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH`pi * inv x = pi / x`];ALL_TAC] THEN
    RULE_ASSUM_TAC(ONCE_SIMP_RULE[REAL_ARITH`&0 < x <=> &0 < &2 * x`]) THEN
    RULE_ASSUM_TAC (SIMP_RULE[REAL_ARITH`a < pi / &2 <=> &2 * a < pi`])
    THEN ASM_SIMP_TAC[SIN_POS_PI]
);;

let SIN_POS_LT_PI2 = prove
 (`!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SIN_POS_PI THEN
  ASM_REAL_ARITH_TAC);;

let DELTA_P_INCRE = prove
(`!t:num.
    1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
    &0 < &t /\ &(t + 1) <= pi / (&4 * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))) - &1 / &2 ==>
   &0 < measurement (tau k:(N)qstate) (state_after_giter k (t + 1):(N)qstate)
    - measurement (tau k:(N)qstate) (state_after_giter k t:(N)qstate)`,
    SIMP_TAC[TAU_MEASUREMENT_PROB] THEN REPEAT STRIP_TAC THEN SIMP_TAC[REAL_ADD_LDISTRIB;GSYM REAL_OF_NUM_CLAUSES]
    THEN SIMP_TAC[REAL_ARITH`(a + &2 * &1) + &1 = a + &3`] THEN MATCH_MP_TAC SIN_POW2_INCRE THEN
    ASM_SIMP_TAC[] THEN POP_ASSUM MP_TAC THEN SIMP_TAC[GSYM REAL_OF_NUM_CLAUSES] THEN
    SIMP_TAC[REAL_ARITH`a + &1 <= b - &1 / &2 <=> a <= b - &3 / &2`] THEN SIMP_TAC[REAL_ARITH`a <= b - &3 / &2
     ==> a < b - &1`] THEN STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM ASN_0] THEN ONCE_REWRITE_TAC[GSYM ASN_1] THEN
     STRIP_TAC THENL[MATCH_MP_TAC ASN_MONO_LT THEN SIMP_TAC[REAL_ARITH`-- &1 <= &0`] THEN STRIP_TAC THENL[
     ONCE_REWRITE_TAC[GSYM SQRT_1] THEN SIMP_TAC[GSYM SQRT_DIV] THEN MATCH_MP_TAC SQRT_POS_LT THEN
   SIMP_TAC[real_div;REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_INV THEN SIMP_TAC[REAL_OF_NUM_LT] THEN
   MATCH_MP_TAC (ARITH_RULE`1 <= a ==> 0 < a`) THEN SIMP_TAC[DIMINDEX_GE_1];ALL_TAC] THEN ONCE_REWRITE_TAC[GSYM SQRT_1]
   THEN SIMP_TAC[GSYM SQRT_DIV] THEN MATCH_MP_TAC SQRT_MONO_LE THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN
   MATCH_MP_TAC REAL_INV_LE_1 THEN SIMP_TAC[DIMINDEX_GE_1;REAL_OF_NUM_LE];ALL_TAC] THEN MATCH_MP_TAC ASN_MONO_LT
   THEN SIMP_TAC[REAL_LE_REFL] THEN STRIP_TAC THENL[MATCH_MP_TAC (REAL_ARITH`&0 < a ==> -- &1 <= a`) THEN
   ONCE_REWRITE_TAC[GSYM SQRT_1] THEN SIMP_TAC[GSYM SQRT_DIV] THEN MATCH_MP_TAC SQRT_POS_LT THEN
   SIMP_TAC[real_div;REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_INV THEN SIMP_TAC[REAL_OF_NUM_LT] THEN
   MATCH_MP_TAC (ARITH_RULE`1 <= a ==> 0 < a`) THEN SIMP_TAC[DIMINDEX_GE_1];ALL_TAC] THEN ONCE_REWRITE_TAC[GSYM SQRT_1]
   THEN SIMP_TAC[GSYM SQRT_DIV] THEN MATCH_MP_TAC SQRT_MONO_LT THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN
   MATCH_MP_TAC REAL_INV_LT_1 THEN SIMP_TAC[REAL_OF_NUM_LT] THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
   THEN SIMP_TAC[ARITH_RULE`1 = 2 EXP 0`] THEN SIMP_TAC[LT_EXP] THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= a ==> 0 < a`]
   THEN ARITH_TAC
);;


let REAL_MUL_LT0 = prove
(`!a b.a < &0 /\ &0 < b ==> a * b < &0`,
REPEAT STRIP_TAC THEN SIMP_TAC[GSYM REAL_NEG_GT0;REAL_NEG_LMUL] THEN
MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_NEG_GT0]
);;

let SIN_POW2_DECRE = prove
(`!n:num x:real. &0 < x /\ x < pi / &2
    /\ pi / (&4 * x) - & 1 < &n /\ &n < pi / (&2 * x) - &1 ==>
    &0 < sin((&2 * &n + &1) * x) pow 2 - sin((&2 * &n + &3) * x) pow 2`,
    REPEAT STRIP_TAC THEN SIMP_TAC[SIN_POW2_SUB;REAL_ARITH`a * x + b * x = (a + b) * x:real`;
    REAL_ARITH`a * x - b * x = (a - b) * x:real`;REAL_ARITH`(&2 * a + &1) + &2 * a + &3  = &4 * a + &4`;
    REAL_ARITH`(&2 * a + &1) - (&2 * a + &3)  = -- &2`; REAL_ARITH`-- &2 * x = --(&2 * x)`;SIN_NEG] THEN
    SIMP_TAC[GSYM REAL_NEG_RMUL;REAL_NEG_GT0] THEN MP_TAC (SPEC `&2 * x` SIN_POS_PI) THEN
    RULE_ASSUM_TAC(ONCE_SIMP_RULE[REAL_ARITH`&0 < x <=> &0 < &2 * x`;REAL_ARITH `a < pi / &2 <=> &2 * a < pi`])
    THEN ASM_SIMP_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC REAL_MUL_LT0 THEN ASM_SIMP_TAC[] THEN
    SIMP_TAC[GSYM REAL_NEG_GT0;GSYM SIN_NEG] THEN ONCE_SIMP_TAC[GSYM SIN_PERIODIC] THEN
    MATCH_MP_TAC SIN_POS_PI THEN STRIP_TAC THENL[SIMP_TAC[REAL_ARITH`&0 < --a + b <=> a < b`] THEN
    SIMP_TAC[REAL_ARITH`&4 * &n + &4 = &4 * (&n + &1)`] THEN SIMP_TAC[REAL_ARITH`(&4 * a) * x < &2 * pi <=> a * x  < pi / &2`]
    THEN RULE_ASSUM_TAC(ONCE_SIMP_RULE[REAL_ARITH`&0 < &2 * x <=> &0 < x`]) THEN
    RULE_ASSUM_TAC(SIMP_RULE[REAL_ARITH`b < a - &1 <=> b + &1 < a`]) THEN UNDISCH_TAC`&n + &1 < pi / (&2 * x)`
    THEN STRIP_TAC THEN SIMP_TAC[REAL_ARITH`a < pi / &2 <=> &2 * a < pi`] THEN MATCH_MP_TAC REAL_LT_RCANCEL_IMP
    THEN EXISTS_TAC`&1 / (&2 * x)` THEN SIMP_TAC[REAL_ARITH`(&2 * a * x) * b= a * (&2 * x * b)`] THEN
    ASM_SIMP_TAC[REAL_FIELD`&0 < X ==> &2 * X * &1 / (&2 * X) = &1`] THEN
    RULE_ASSUM_TAC(ONCE_SIMP_RULE[REAL_ARITH`&0 < x <=> &0 < &2 * x`]) THEN
    ASM_SIMP_TAC[REAL_ARITH`&0 < x ==> &1 / x = inv x`;REAL_LT_INV] THEN
    ASM_SIMP_TAC[REAL_ARITH`&0 < x ==> pi * inv x = pi / x`;REAL_MUL_RID];ALL_TAC] THEN
    SIMP_TAC[REAL_ARITH`-- a + &2 * pi < pi <=> pi < a`] THEN SIMP_TAC[REAL_ARITH`(&4 * &n + &4) * x = (&n + &1) * &4 * x`]
    THEN UNDISCH_TAC`pi / (&4 * x) - &1 < &n` THEN SIMP_TAC[REAL_ARITH`a - &1 < b <=> a < b + &1`] THEN
    RULE_ASSUM_TAC(ONCE_SIMP_RULE[REAL_ARITH`&0 < &2 * x <=> &0 < &4 * x`]) THEN STRIP_TAC THEN
    MATCH_MP_TAC REAL_LT_RCANCEL_IMP THEN EXISTS_TAC`&1 / (&4 * x)` THEN SIMP_TAC[REAL_ARITH`(a * &4 * x) * b= a * (&4 * x * b)`]
    THEN ASM_SIMP_TAC[REAL_ARITH`&0 < x ==> &1 / x = inv x`;REAL_LT_INV] THEN
    ASM_SIMP_TAC[REAL_FIELD`&0 < &4 * x ==> a * &4 * x * inv (&4 * x) = a * &1`;REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH`&0 < a ==> pi * inv a =  pi / a`]
);;

let DELTA_P_DECRE = prove
(`!t:num.
    1 <= k /\ k <= dimindex(:(2,N)finite_pow) /\
    pi / (&4 * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))) - &1 / &2 <= &t /\
    &t <= pi / (&2 * asn (&1 / sqrt (&(dimindex (:(2,N)finite_pow))))) - &3 / &2 ==>
   &0 < measurement (tau k:(N)qstate) (state_after_giter k t:(N)qstate)
    - measurement (tau k:(N)qstate) (state_after_giter k (t+1):(N)qstate)`,
    SIMP_TAC[TAU_MEASUREMENT_PROB] THEN REPEAT STRIP_TAC THEN SIMP_TAC[REAL_ADD_LDISTRIB;GSYM REAL_OF_NUM_CLAUSES]
    THEN SIMP_TAC[REAL_ARITH`(a + &2 * &1) + &1 = a + &3`] THEN MATCH_MP_TAC SIN_POW2_DECRE THEN
    ASM_SIMP_TAC[REAL_ARITH`a - &1 / &2 <= b ==> a - &1 < b`;REAL_ARITH`b <= a - &3 / &2 ==> b < a - &1`] THEN
    ONCE_REWRITE_TAC[GSYM ASN_0] THEN ONCE_REWRITE_TAC[GSYM ASN_1] THEN
     STRIP_TAC THENL[MATCH_MP_TAC ASN_MONO_LT THEN SIMP_TAC[REAL_ARITH`-- &1 <= &0`] THEN STRIP_TAC THENL[
     ONCE_REWRITE_TAC[GSYM SQRT_1] THEN SIMP_TAC[GSYM SQRT_DIV] THEN MATCH_MP_TAC SQRT_POS_LT THEN
   SIMP_TAC[real_div;REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_INV THEN SIMP_TAC[REAL_OF_NUM_LT] THEN
   MATCH_MP_TAC (ARITH_RULE`1 <= a ==> 0 < a`) THEN SIMP_TAC[DIMINDEX_GE_1];ALL_TAC] THEN ONCE_REWRITE_TAC[GSYM SQRT_1]
   THEN SIMP_TAC[GSYM SQRT_DIV] THEN MATCH_MP_TAC SQRT_MONO_LE THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN
   MATCH_MP_TAC REAL_INV_LE_1 THEN SIMP_TAC[DIMINDEX_GE_1;REAL_OF_NUM_LE];ALL_TAC] THEN MATCH_MP_TAC ASN_MONO_LT
   THEN SIMP_TAC[REAL_LE_REFL] THEN STRIP_TAC THENL[MATCH_MP_TAC (REAL_ARITH`&0 < a ==> -- &1 <= a`) THEN
   ONCE_REWRITE_TAC[GSYM SQRT_1] THEN SIMP_TAC[GSYM SQRT_DIV] THEN MATCH_MP_TAC SQRT_POS_LT THEN
   SIMP_TAC[real_div;REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LT_INV THEN SIMP_TAC[REAL_OF_NUM_LT] THEN
   MATCH_MP_TAC (ARITH_RULE`1 <= a ==> 0 < a`) THEN SIMP_TAC[DIMINDEX_GE_1];ALL_TAC] THEN ONCE_REWRITE_TAC[GSYM SQRT_1]
   THEN SIMP_TAC[GSYM SQRT_DIV] THEN MATCH_MP_TAC SQRT_MONO_LT THEN SIMP_TAC[real_div;REAL_MUL_LID] THEN
   MATCH_MP_TAC REAL_INV_LT_1 THEN SIMP_TAC[REAL_OF_NUM_LT] THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2]
   THEN SIMP_TAC[ARITH_RULE`1 = 2 EXP 0`] THEN SIMP_TAC[LT_EXP] THEN SIMP_TAC[DIMINDEX_GE_1;ARITH_RULE`1 <= a ==> 0 < a`]
   THEN ARITH_TAC
);;


(* ------------------------------------------------------------------------- *)
(* Application of Grover algorithm         *)
(* ------------------------------------------------------------------------- *)
let FENJIEZUIYOU = prove
(`!t:num.
  (&2 * &t + &1) * asn (&1 / sqrt (&(dimindex (:(2,4)finite_pow)))) <= pi ==>
  measurement (tau 11:(4)qstate) (state_after_giter 11 t:(4)qstate) <=
   measurement (tau 11:(4)qstate) (state_after_giter 11 (
   num_of_real ((pi / (&4 *  asn (&1 / sqrt (&(dimindex (:(2,4)finite_pow)))))) - &1 / &2)):(4)qstate) \/
   measurement (tau 11:(4)qstate) (state_after_giter 11 t:(4)qstate) <=
   measurement (tau 11:(4)qstate) (state_after_giter 11 (
   num_of_real ((pi / (&4 *  asn (&1 / sqrt (&(dimindex (:(2,4)finite_pow)))))) - &1 / &2) + 1):(4)qstate)`,
   REPEAT STRIP_TAC THEN MATCH_MP_TAC OPT_GROVER_STEPS THEN POP_ASSUM MP_TAC THEN
   SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_4;DIMINDEX_2] THEN
   SIMP_TAC[REAL_ARITH`&2 * &2 + &1 = &5`] THEN SIMP_TAC[ARITH_RULE`2 EXP 4 = 16`] THEN
   SIMP_TAC[ARITH_RULE`1 <= 11 /\ 11 <= 16`] THEN REWRITE_TAC[REAL_ARITH`&16 = &4 pow 2`] THEN
   SIMP_TAC[REAL_ARITH`&0 <= &4`;POW_2_SQRT]
);;

let INCRE_0_1 = prove
(`measurement (tau 11:(4)qstate) (state_after_giter 11 0:(4)qstate) <
 measurement (tau 11:(4)qstate) (state_after_giter 11 1:(4)qstate)`,
 ONCE_SIMP_TAC[REAL_ARITH`a < b <=> &0 < b - a`] THEN ONCE_REWRITE_TAC[ARITH_RULE`1 = 0 + 1`] THEN
 MATCH_MP_TAC DELTA_P_INCRE THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;DIMINDEX_4] THEN
 SIMP_TAC[ARITH_RULE`2 EXP 4 = 16 /\ 0 + 1 = 1`] THEN REWRITE_TAC[REAL_ARITH`&16 = &4 pow 2`] THEN
 SIMP_TAC[REAL_ARITH`&0 <= &4`;POW_2_SQRT] THEN SIMP_TAC[ARITH_RULE`1 <= 11 /\ 11 <= 16`] THEN
 SIMP_TAC[REAL_ARITH`&1 <= a - &1 / &2 <=> &3 / &2 <= a`] THEN
 SIMP_TAC[REAL_FIELD`&3 / &2 <= a / (&4 * b) <=> &6 <= a / b`] THEN
 SUBGOAL_THEN`&0 < asn(&1 / &4)`ASSUME_TAC
 THENL[ONCE_REWRITE_TAC[GSYM ASN_0] THEN MATCH_MP_TAC ASN_MONO_LT THEN REAL_ARITH_TAC;ALL_TAC] THEN
 ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN SIMP_TAC[REAL_ARITH`&6 * a <= b <=> a <= b / &6`] THEN
 SUBGOAL_THEN`pi / &6 = asn(sin(pi / &6))`SUBST1_TAC THENL[MATCH_MP_TAC (GSYM ASN_SIN)
 THEN SIMP_TAC[REAL_ARITH`&0 < a ==> --(a / &2) <= a / &6 /\ a / &6 <= a / &2`;PI_POS];ALL_TAC] THEN
 MATCH_MP_TAC ASN_MONO_LE THEN SIMP_TAC[SIN_BOUNDS;SIN_PI6] THEN SIMP_TAC[REAL_ARITH`&1 / &4 <=
 a / &4 <=> &1 <= a`] THEN REAL_ARITH_TAC
);;

let INCRE_1_2 = prove
(`measurement (tau 11:(4)qstate) (state_after_giter 11 1:(4)qstate) <
 measurement (tau 11:(4)qstate) (state_after_giter 11 2:(4)qstate)`,
 ONCE_SIMP_TAC[REAL_ARITH`a < b <=> &0 < b - a`] THEN SIMP_TAC[ARITH_RULE`2 = 1 + 1`] THEN
 MATCH_MP_TAC DELTA_P_INCRE THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;DIMINDEX_4] THEN
 SIMP_TAC[ARITH_RULE`2 EXP 4 = 16 /\ 1 + 1 = 2`] THEN REWRITE_TAC[REAL_ARITH`&16 = &4 pow 2`] THEN
 SIMP_TAC[REAL_ARITH`&0 <= &4`;POW_2_SQRT] THEN SIMP_TAC[ARITH_RULE`1 <= 11 /\ 11 <= 16`] THEN
 SIMP_TAC[REAL_ARITH`&0 < &1`] THEN SIMP_TAC[REAL_ARITH`&2 <= a - &1 / &2 <=> &5 / &2 <= a`] THEN
 SIMP_TAC[REAL_ARITH`&5 / &2 <= a / (&4 * b) <=> &10 <= a / (&4 * b) * &4`] THEN
 SIMP_TAC[REAL_FIELD`a / (&4 * b) * &4 = a / b`] THEN SUBGOAL_THEN`&0 < asn(&1 / &4)`ASSUME_TAC
 THENL[ONCE_REWRITE_TAC[GSYM ASN_0] THEN MATCH_MP_TAC ASN_MONO_LT THEN REAL_ARITH_TAC;ALL_TAC] THEN
 ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN SIMP_TAC[REAL_ARITH`&10 * a <= b <=> a <= b / &10`] THEN
 SUBGOAL_THEN`pi / &10 = asn(sin(pi / &10))`SUBST1_TAC THENL[MATCH_MP_TAC (GSYM ASN_SIN)
 THEN SIMP_TAC[REAL_ARITH`&0 < a ==> --(a / &2) <= a / &10 /\ a / &10 <= a / &2`;PI_POS];ALL_TAC] THEN
 MATCH_MP_TAC ASN_MONO_LE THEN SIMP_TAC[SIN_BOUNDS;SIN_PI10] THEN SIMP_TAC[REAL_ARITH`&1 / &4 <=
 a / &4 <=> &1 <= a`] THEN SIMP_TAC[REAL_ARITH`&1 <= a - &1 <=> &2 <= a`] THEN
 SUBGOAL_THEN`&2 = sqrt(&4)`SUBST1_TAC THENL[SIMP_TAC[REAL_ARITH`&4 = &2 pow 2`] THEN
 MATCH_MP_TAC (GSYM POW_2_SQRT) THEN REAL_ARITH_TAC;ALL_TAC] THEN
 SIMP_TAC[REAL_ARITH`&4 <= &5`;SQRT_MONO_LE] THEN REAL_ARITH_TAC
);;

let DECRE_4_3 = prove
(`measurement (tau 11:(4)qstate) (state_after_giter 11 4:(4)qstate) <
 measurement (tau 11:(4)qstate) (state_after_giter 11 3:(4)qstate)`,
 ONCE_SIMP_TAC[REAL_ARITH`a < b <=> &0 < b - a`] THEN SIMP_TAC[ARITH_RULE`4 = 3 + 1`] THEN
 MATCH_MP_TAC DELTA_P_DECRE THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;DIMINDEX_4] THEN
 SIMP_TAC[ARITH_RULE`2 EXP 4 = 16 /\ 3 + 1 = 4`] THEN REWRITE_TAC[REAL_ARITH`&16 = &4 pow 2`] THEN
 SIMP_TAC[REAL_ARITH`&0 <= &4`;POW_2_SQRT] THEN SIMP_TAC[ARITH_RULE`1 <= 11 /\ 11 <= 16`] THEN
 SIMP_TAC[REAL_ARITH`&3 <= a - &3 / &2 <=> &9 / &2 <= a`] THEN
 SIMP_TAC[REAL_ARITH`a - &1 / &2 <= &3 <=> a <= &7 / &2`] THEN
 SIMP_TAC[REAL_FIELD`&9 / &2 <= a / (&2 * b) <=> &9 <= a /  b`] THEN
 SIMP_TAC[REAL_FIELD`a / (&4 * b) <= &7 / &2 <=> a / b <= &14`] THEN
 SUBGOAL_THEN`&0 < asn(&1 / &4)`ASSUME_TAC THENL[ONCE_REWRITE_TAC[GSYM ASN_0] THEN
 MATCH_MP_TAC ASN_MONO_LT THEN REAL_ARITH_TAC;ALL_TAC] THEN
 ASM_SIMP_TAC[REAL_LE_RDIV_EQ;REAL_LE_LDIV_EQ] THEN SIMP_TAC[REAL_ARITH`&9 * a <= b
 <=> a <= b / &9`] THEN SIMP_TAC[REAL_ARITH`b <= &14 * a <=> b / &14 <= a`] THEN
 SUBGOAL_THEN`pi / &14 = asn(sin(pi / &14))`SUBST1_TAC THENL[MATCH_MP_TAC (GSYM ASN_SIN) THEN
 SIMP_TAC[REAL_ARITH`&0 < a ==> --(a / &2) <= a / &14 /\ a / &14 <= a / &2`;PI_POS];ALL_TAC] THEN
 SUBGOAL_THEN`pi / &9 = asn(sin(pi / &9))`SUBST1_TAC THENL[MATCH_MP_TAC (GSYM ASN_SIN) THEN
 SIMP_TAC[REAL_ARITH`&0 < a ==> --(a / &2) <= a / &9 /\ a / &9 <= a / &2`;PI_POS];ALL_TAC] THEN
 STRIP_TAC THENL[MATCH_MP_TAC ASN_MONO_LE THEN SIMP_TAC[SIN_BOUNDS;REAL_ARITH`&1 / &4 <= &1`] THEN
 MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC`abs(sin(pi / &14))` THEN SIMP_TAC[REAL_ABS_LE] THEN
 ONCE_REWRITE_TAC[REAL_ARITH`&1 / &4 = abs(&1 / &4)`] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
 EXISTS_TAC`abs(pi / &14)` THEN SIMP_TAC[REAL_ABS_SIN_BOUND_LE] THEN
 SIMP_TAC[PI_POS;REAL_ARITH`&0 < a ==> abs(a / &14) = a / &14`] THEN
 SIMP_TAC[REAL_ARITH`abs(&1 / &4) = &1 / &4`] THEN SIMP_TAC[REAL_ARITH`a / &14 <= &1 / &4
 <=> a <= &14 / &4`] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&13493037705 / &4294967296 +
 inv (&2 pow 32)` THEN SIMP_TAC[REAL_ARITH`a <= b + c <=> a - b <= c:real`] THEN
 STRIP_TAC THENL[MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC`abs(pi - &13493037705 / &4294967296)` THEN
 SIMP_TAC[REAL_ABS_LE;PI_APPROX_32];ALL_TAC] THEN REAL_ARITH_TAC;ALL_TAC] THEN
 MATCH_MP_TAC ASN_MONO_LE THEN SIMP_TAC[SIN_BOUNDS;REAL_ARITH`-- &1 <= &1 / &4`] THEN
 MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC`sin(pi / &10)` THEN STRIP_TAC THENL[
 SIMP_TAC[SIN_PI10] THEN SIMP_TAC[REAL_ARITH`&1 / &4 <= (a - &1) / &4 <=> &2 <= a`] THEN
 MATCH_MP_TAC REAL_LE_RSQRT THEN REAL_ARITH_TAC;ALL_TAC] THEN
 MATCH_MP_TAC SIN_MONO_LE THEN SIMP_TAC[PI_POS;REAL_FIELD`&0 < pi ==> --(pi / &2) <= pi / &10`] THEN
 SIMP_TAC[PI_POS;REAL_FIELD`&0 < pi ==> pi / &10 <= pi / &9`] THEN
 SIMP_TAC[PI_POS;REAL_FIELD`&0 < pi ==> pi / &9 <= pi / &2`]
);;

let DECRE_5_4 = prove
(`measurement (tau 11:(4)qstate) (state_after_giter 11 5:(4)qstate) <
 measurement (tau 11:(4)qstate) (state_after_giter 11 4:(4)qstate)`,
 ONCE_SIMP_TAC[REAL_ARITH`a < b <=> &0 < b - a`] THEN SIMP_TAC[ARITH_RULE`5 = 4 + 1`] THEN
 MATCH_MP_TAC DELTA_P_DECRE THEN SIMP_TAC[DIMINDEX_FINITE_POW;DIMINDEX_2;DIMINDEX_4] THEN
 SIMP_TAC[ARITH_RULE`2 EXP 4 = 16 /\ 4 + 1 = 5`] THEN REWRITE_TAC[REAL_ARITH`&16 = &4 pow 2`] THEN
 SIMP_TAC[REAL_ARITH`&0 <= &4`;POW_2_SQRT] THEN SIMP_TAC[ARITH_RULE`1 <= 11 /\ 11 <= 16`] THEN
 SIMP_TAC[REAL_ARITH`&4 <= a - &3 / &2 <=> &11 / &2 <= a`] THEN
 SIMP_TAC[REAL_ARITH`a - &1 / &2 <= &4 <=> a <= &9 / &2`] THEN
 SIMP_TAC[REAL_FIELD`&11 / &2 <= a / (&2 * b) <=> &11 <= a /  b`] THEN
 SIMP_TAC[REAL_FIELD`a / (&4 * b) <= &9 / &2 <=> a / b <= &18`] THEN
 SUBGOAL_THEN`&0 < asn(&1 / &4)`ASSUME_TAC THENL[ONCE_REWRITE_TAC[GSYM ASN_0] THEN
 MATCH_MP_TAC ASN_MONO_LT THEN REAL_ARITH_TAC;ALL_TAC] THEN
 ASM_SIMP_TAC[REAL_LE_RDIV_EQ;REAL_LE_LDIV_EQ] THEN SIMP_TAC[REAL_ARITH`&11 * a <= b
 <=> a <= b / &11`] THEN SIMP_TAC[REAL_ARITH`b <= &18 * a <=> b / &18 <= a`] THEN
 SUBGOAL_THEN`pi / &11 = asn(sin(pi / &11))`SUBST1_TAC THENL[MATCH_MP_TAC (GSYM ASN_SIN) THEN
 SIMP_TAC[REAL_ARITH`&0 < a ==> --(a / &2) <= a / &11 /\ a / &11 <= a / &2`;PI_POS];ALL_TAC] THEN
 SUBGOAL_THEN`pi / &18 = asn(sin(pi / &18))`SUBST1_TAC THENL[MATCH_MP_TAC (GSYM ASN_SIN) THEN
 SIMP_TAC[REAL_ARITH`&0 < a ==> --(a / &2) <= a / &18 /\ a / &18 <= a / &2`;PI_POS];ALL_TAC] THEN
 STRIP_TAC THENL[MATCH_MP_TAC ASN_MONO_LE THEN SIMP_TAC[SIN_BOUNDS;REAL_ARITH`&1 / &4 <= &1`] THEN
 MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC`abs(sin(pi / &18))` THEN SIMP_TAC[REAL_ABS_LE] THEN
 ONCE_REWRITE_TAC[REAL_ARITH`&1 / &4 = abs(&1 / &4)`] THEN MATCH_MP_TAC REAL_LE_TRANS THEN
 EXISTS_TAC`abs(pi / &18)` THEN SIMP_TAC[REAL_ABS_SIN_BOUND_LE] THEN
 SIMP_TAC[PI_POS;REAL_ARITH`&0 < a ==> abs(a / &18) = a / &18`] THEN
 SIMP_TAC[REAL_ARITH`abs(&1 / &4) = &1 / &4`] THEN SIMP_TAC[REAL_ARITH`a / &18 <= &1 / &4
 <=> a <= &18 / &4`] THEN MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&13493037705 / &4294967296 +
 inv (&2 pow 32)` THEN SIMP_TAC[REAL_ARITH`a <= b + c <=> a - b <= c:real`] THEN
 STRIP_TAC THENL[MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC`abs(pi - &13493037705 / &4294967296)` THEN
 SIMP_TAC[REAL_ABS_LE;PI_APPROX_32];ALL_TAC] THEN REAL_ARITH_TAC;ALL_TAC] THEN
 MATCH_MP_TAC ASN_MONO_LE THEN SIMP_TAC[SIN_BOUNDS;REAL_ARITH`-- &1 <= &1 / &4`] THEN
 MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC`sin(pi / &12)` THEN STRIP_TAC THENL[
 ONCE_REWRITE_TAC[REAL_ARITH`&1 / &4 = abs(&1 / &4)`] THEN
 SUBGOAL_THEN`sin(pi / &12) = abs(sin(pi / &12))`SUBST1_TAC THENL[
 MATCH_MP_TAC (REAL_ARITH`&0 < x ==> x = abs(x)`) THEN MATCH_MP_TAC SIN_POS_PI2 THEN
 SIMP_TAC[PI_POS;REAL_FIELD`&0 < pi ==> pi / &12 < pi / &2`;REAL_FIELD`&0 < pi ==>
 &0 < pi / &12`];ALL_TAC] THEN SIMP_TAC[REAL_LE_SQUARE_ABS] THEN
 SIMP_TAC[REAL_ARITH`(&1 / &4) pow 2 = &1 / &16`] THEN
 SUBGOAL_THEN`sin (pi / &12) pow 2 = (&2 - sqrt(&3)) / &4`SUBST1_TAC THENL[
 ONCE_SIMP_TAC[REAL_ARITH`a = b <=> &1 - &2 * a = &1 - &2 * b`] THEN
 SIMP_TAC[GSYM COS_DOUBLE_SIN;REAL_ARITH`&2 * pi / &12 = pi / &6`;COS_PI6] THEN
 REAL_ARITH_TAC;ALL_TAC] THEN
 SIMP_TAC[REAL_ARITH`&1 / &16 <= a / &4 <=> &1 <= &4 * a`] THEN
 SIMP_TAC[REAL_ARITH`&1 <= &4 * (&2 - a) <=> a <= &7 / &4`] THEN
 MATCH_MP_TAC REAL_LE_LSQRT THEN REAL_ARITH_TAC;ALL_TAC] THEN
 MATCH_MP_TAC SIN_MONO_LE THEN SIMP_TAC[PI_POS;REAL_FIELD`&0 < pi ==> --(pi / &2) <= pi / &12`] THEN
 SIMP_TAC[PI_POS;REAL_FIELD`&0 < pi ==> pi / &12 <= pi / &11`] THEN
 SIMP_TAC[PI_POS;REAL_FIELD`&0 < pi ==> pi / &11 <= pi / &2`]
);;
