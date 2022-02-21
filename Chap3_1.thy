theory Chap3_1
imports Main
begin

type_synonym vname = string

datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n"
| "aval (V v) s = s v"
| "aval (Plus e1 e2) s = aval e1 s + aval e2 s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>_. 0)"

value "aval (Plus (Plus (N 3) (V ''x'')) (V ''y'')) (((\<lambda>_. 0)(''x'' := 1))(''y'' := 2))"

value "aval (Plus (Plus (N 3) (V ''x'')) (V ''y'')) <''x'' := 1, ''y'' := 2>"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n"
| "asimp_const (V x) = V x"
| "asimp_const (Plus a1 a2) =
  (case (asimp_const a1, asimp_const a2) of
    (N n1, N n2) \<Rightarrow> N (n1 + n2)
    | (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply (induction a)
  by (auto split: aexp.split)

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)"
| "plus (N i) a = (if i=0 then a else Plus (N i) a)"
| "plus a (N i) = (if i=0 then a else Plus a (N i))"
| "plus a1 a2 = Plus a1 a2"

lemma aval_plus: "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply (induction rule: plus.induct)
  by auto

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n"
| "asimp (V x) = V x"
| "asimp (Plus a1 a2) = plus (asimp a1) (asimp a2)"

lemma "aval (asimp a) s = aval a s"
  apply (induction a)
  by (auto simp add: aval_plus)

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N n) = True"
| "optimal (V x) = True"
| "optimal (Plus a1 a2) =
  (case (a1, a2) of
    (N _, N _) \<Rightarrow> False
    | _ \<Rightarrow> optimal a1 \<and> optimal a2)"

lemma "optimal (asimp_const a)"
  apply (induction a)
    apply simp+
  apply (case_tac "asimp_const a1")
    apply simp_all
  apply (case_tac "asimp_const a2")
  by simp+

fun nplus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"nplus (N n1) (N n2) = N (n1 + n2)"
| "nplus (N n1) (Plus a (N n2)) = Plus a (N (n1 + n2))"
| "nplus (N n) a = Plus a (N n)"
| "nplus (Plus a (N n1)) (N n2) = Plus a (N (n1 + n2))"
| "nplus (Plus a1 (N n1)) (Plus a2 (N n2)) = Plus (Plus a1 a2) (N (n1 + n2))"
| "nplus (Plus a1 (N n)) a2 = Plus (Plus a1 a2) (N n)"
| "nplus a1 (Plus a2 (N n)) = Plus (Plus a1 a2) (N n)"
| "nplus a1 a2 = Plus a1 a2"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N n) = N n"
| "full_asimp (V x) = V x"
| "full_asimp (Plus a1 a2) = nplus (full_asimp a1) (full_asimp a2)"

lemma "full_asimp (Plus (N 1) (Plus (V x) (N 2))) = Plus (V x) (N 3)"
  by simp

fun without_N :: "aexp \<Rightarrow> bool" where
"without_N (N _) = False"
| "without_N (V _) = True"
| "without_N (Plus a1 a2) = (without_N a1 \<and> without_N a2)"

fun in_normal_form :: "aexp \<Rightarrow> bool" where
"in_normal_form (N _) = True"
| "in_normal_form (V _) = True"
| "in_normal_form (Plus a1 a2) = (without_N a1 \<and> (without_N a2 \<or> (\<exists>n. a2 = N n)))"

lemma nplus_normal:
  "\<lbrakk> in_normal_form a1; in_normal_form a2 \<rbrakk> \<Longrightarrow> in_normal_form (nplus a1 a2)"
  apply (cases "(a1, a2)" rule: nplus.cases)
  by auto

lemma "in_normal_form (full_asimp a)"
  apply (induction a)
    apply simp+
  using nplus_normal by blast

lemma "aval (full_asimp a) s = aval a s"
  apply (induction a)
    apply simp+
  apply (case_tac "(full_asimp a1, full_asimp a2)" rule: nplus.cases)
  by auto

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N n) = (N n)"
| "subst x a (V y) = (if x = y then a else V y)"
| "subst x a (Plus a1 a2) = Plus (subst x a a1) (subst x a a2)"

lemma subst_comm: "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply (induction e)
  by simp+

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply (induction e)
  (*using [[simp_trace]]*)
  by simp+

datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | PostInc aexp2 | Div aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val * state) option" where
"aval2 (N2 n) s = Some (n, s)"
| "aval2 (V2 x) s = Some (s x, s)"
| "aval2 (Plus2 a1 a2) s = 
  (case aval2 a1 s of
    None \<Rightarrow> None
    | Some (v1, s') \<Rightarrow>
      (case aval2 a2 s' of
        None \<Rightarrow> None
        | Some (v2, s'') \<Rightarrow> Some (v1 + v2, s'')
      )
  )"
| "aval2 (PostInc (V2 x)) s = Some (s x, s(x := (s x)+1))"
| "aval2 (Div a1 a2) s =
  (case aval2 a1 s of
    None \<Rightarrow> None
    | Some (v1, s') \<Rightarrow>
      (case aval2 a2 s' of
        None \<Rightarrow> None
        | Some (v2, s'') \<Rightarrow> if v2=0 then None else Some (v1 div v2, s'')
      )
  )"

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl n) _ = n"
| "lval (Vl x) s = s x"
| "lval (Plusl a1 a2) s = lval a1 s + lval a2 s"
| "lval (LET x a e) s = lval e (s(x := lval a s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl n) = N n"
| "inline (Vl x) = V x"
| "inline (Plusl a1 a2) = Plus (inline a1) (inline a2)"
| "inline (LET x a e) = subst x (inline a) (inline e)"

value "inline (LET ''x'' (Vl ''y'') (LET ''y'' (Nl 0) (Vl ''x'')))"

lemma "aval (inline e) s = lval e s"
  apply (induction e arbitrary: s)
     apply simp+
  using subst_comm by presburger

end