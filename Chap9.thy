theory Chap9
  imports Main "HOL-IMP.Star"
begin

type_synonym vname = string
datatype val = Iv int | Bv bool
type_synonym state = "vname \<Rightarrow> val"
datatype expr = N int | V vname | Bc bool | Not expr | Plus expr expr | And expr expr | Less expr expr

inductive tval :: "expr \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"tval (N n) s (Iv n)"
| "tval (V x) s (s x)"
| "tval (Bc b) s (Bv b)"
| "tval e s (Bv b) \<Longrightarrow> tval (Not e) s (Bv (\<not>b))"
| "\<lbrakk> tval e1 s (Iv n1); tval e2 s (Iv n2) \<rbrakk> \<Longrightarrow> tval (Plus e1 e2) s (Iv (n1+n2))"
| "\<lbrakk> tval e1 s (Bv b1); tval e2 s (Bv b2) \<rbrakk> \<Longrightarrow> tval (And e1 e2) s (Bv (b1\<and>b2))"
| "\<lbrakk> tval e1 s (Iv n1); tval e2 s (Iv n2) \<rbrakk> \<Longrightarrow> tval (Less e1 e2) s (Bv (n1<n2))"

inductive_cases [elim!]:
"tval (N n) s v"
"tval (V x) s v"
"tval (Bc b) s v"
"tval (Not e) s v"
"tval (Plus e1 e2) s v"
"tval (And e1 e2) s v"
"tval (Less e1 e2) s v"

datatype com = 
  Skip
  | Assign vname expr ("_ ::= _" [1000, 61] 61)
  | Seq com com ("_;;/ _"  [60, 61] 60)
  | If expr com com ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
  | While expr com ("(WHILE _/ DO _)"  [0, 61] 61)

inductive step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
Assign: "tval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (Skip, s(x := v))"
| Seq1: "(Skip;; c, s) \<rightarrow> (c, s)"
| Seq2: "(c, s) \<rightarrow> (c', s') \<Longrightarrow> (c;; c'', s) \<rightarrow> (c';; c'', s')"
| IfTrue: "tval b s (Bv True) \<Longrightarrow> (IF b THEN c ELSE c', s) \<rightarrow> (c, s)"
| IfFalse: "tval b s (Bv False) \<Longrightarrow> (IF b THEN c ELSE c', s) \<rightarrow> (c', s)"
| While: "(WHILE b DO c, s) \<rightarrow> (IF b THEN c;;WHILE b DO c ELSE Skip, s)"

datatype ty = Ity | Bty
type_synonym tyenv = "vname \<Rightarrow> ty"

inductive etyping :: "tyenv \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50) where
Ic_ty: "\<Gamma> \<turnstile> (N n) : Ity"
| V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x"
| B_ty: "\<Gamma> \<turnstile> (Bc b) : Bty"
| Not_ty: "\<Gamma> \<turnstile> e : Bty \<Longrightarrow> \<Gamma> \<turnstile> (Not e) : Bty"
| Plus_ty: "\<lbrakk> \<Gamma> \<turnstile> e1 : Ity; \<Gamma> \<turnstile> e2 : Ity \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Plus e1 e2 : Ity"
| And_ty: "\<lbrakk> \<Gamma> \<turnstile> e1 : Bty; \<Gamma> \<turnstile> e2 : Bty \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> And e1 e2 : Bty"
| Less_ty: "\<lbrakk> \<Gamma> \<turnstile> e1 : Ity; \<Gamma> \<turnstile> e2 : Ity \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Less e1 e2 : Bty"

inductive_cases [elim!]:
"\<Gamma> \<turnstile> (N n) : \<tau>"
"\<Gamma> \<turnstile> (V x) : \<tau>"
"\<Gamma> \<turnstile> (Bc b) : \<tau>"
"\<Gamma> \<turnstile> (Not e) : \<tau>"
"\<Gamma> \<turnstile> (Plus e1 e2) : \<tau>"
"\<Gamma> \<turnstile> (And e1 e2) : \<tau>"
"\<Gamma> \<turnstile> (Less e1 e2) : \<tau>"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> Skip"
| Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma> x \<Longrightarrow> \<Gamma> \<turnstile> x ::= a"
\<comment> \<open> previous attempts:
1.
Init_ty: "\<Gamma> x = None \<Longrightarrow> \<Gamma>(x := Some a) \<turnstile> x ::= a"
Assign_ty: "\<Gamma> x = Some typ \<Longrightarrow> \<Gamma> \<turnstile> x ::= a"

makes type safety statement gross, since rtrancl of step might be invalid depending on types of
previous assignments

2.
Assign_ty: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma>(x := \<tau>) \<turnstile> x ::= a"

might allow reading uninit variables in a
\<close>
| Seq_ty: "\<lbrakk> \<Gamma> \<turnstile> c; \<Gamma> \<turnstile> c' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> c;; c'"
| If_ty: "\<lbrakk> \<Gamma> \<turnstile> b : Bty; \<Gamma> \<turnstile> c; \<Gamma> \<turnstile> c' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c ELSE c'"
| While_ty: "\<lbrakk> \<Gamma> \<turnstile> b : Bty; \<Gamma> \<turnstile> c \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"

inductive_cases [elim!]:
"\<Gamma> \<turnstile> Skip"
"\<Gamma> \<turnstile> x ::= a"
"\<Gamma> \<turnstile> c;; c'"
"\<Gamma> \<turnstile> IF b THEN c ELSE c'"
"\<Gamma> \<turnstile> WHILE b DO c"

abbreviation steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y \<equiv> star step x y"

fun type :: "val \<Rightarrow> ty" where
"type (Bv b) = Bty"
| "type (Iv n) = Ity"

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50) where
"\<Gamma> \<turnstile> s \<equiv> \<forall>x. (\<Gamma> x = type (s x))"

lemma epreservation: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>; tval e s v; \<Gamma> \<turnstile> s \<rbrakk> \<Longrightarrow> type v = \<tau>"
  apply (induct e)
  by (auto simp add: styping_def)

declare etyping.intros [intro!]

lemma eprogress: "\<lbrakk> \<Gamma> \<turnstile> e : \<tau>; \<Gamma> \<turnstile> s \<rbrakk> \<Longrightarrow> \<exists>v. tval e s v"
  apply (induct e arbitrary: \<tau>)
        apply (auto intro: tval.intros)[3]
     apply (subgoal_tac "Ex (tval e s)"; clarsimp)
     apply (metis epreservation tval.intros(4) ty.simps(2) type.elims)
    apply (subgoal_tac "Ex (tval e1 s)"; clarsimp)
    apply (subgoal_tac "Ex (tval e2 s)"; clarsimp)
    apply (metis epreservation tval.intros(5) ty.simps(2) type.elims)
   apply (subgoal_tac "Ex (tval e1 s)"; clarsimp)
   apply (subgoal_tac "Ex (tval e2 s)"; clarsimp)
   apply (metis epreservation tval.intros(6) ty.simps(2) type.elims)
  apply (subgoal_tac "Ex (tval e1 s)"; clarsimp)
  apply (subgoal_tac "Ex (tval e2 s)"; clarsimp)
  by (metis epreservation tval.intros(7) ty.simps(2) type.elims)

lemma ctyping_preservation: "\<lbrakk> (c, s) \<rightarrow> (c', s'); \<Gamma> \<turnstile> s; \<Gamma> \<turnstile> c \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> c'"
  apply (induct c s c' s' rule: step.induct[split_format(complete)])
  using ctyping.intros by force+

lemma styping_preservation: "\<lbrakk> (c, s) \<rightarrow> (c', s'); \<Gamma> \<turnstile> s; \<Gamma> \<turnstile> c \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> s'"
  apply (induct rule: step.induct[split_format(complete)])
  apply (clarsimp simp add: styping_def)
  using epreservation styping_def apply presburger
  by auto

lemma progress: "\<lbrakk> \<Gamma> \<turnstile> c; \<Gamma> \<turnstile> s; c \<noteq> Skip \<rbrakk> \<Longrightarrow> \<exists>cs. (c, s) \<rightarrow> cs"
  apply (induct rule: ctyping.induct; simp)
     apply (meson Assign eprogress)
  using Seq1 Seq2 apply blast
   apply (subgoal_tac "\<exists>b'. tval b s (Bv b')")
    apply (metis IfFalse IfTrue)
   apply (metis epreservation eprogress ty.simps(2) type.elims)
  using While by blast

lemma type_sound: "\<lbrakk> (c, s) \<rightarrow>* (c', s'); \<Gamma> \<turnstile> c; \<Gamma> \<turnstile> s; c' \<noteq> Skip \<rbrakk> \<Longrightarrow> \<exists>cs'. (c', s') \<rightarrow> cs'"
  apply (induct rule: star_induct)
  using progress ctyping_preservation styping_preservation by blast+

end