theory Chap7ex
  imports Main Chap7_2 Chap7_3
begin

fun assigned :: "com \<Rightarrow> vname set" where
"assigned SKIP = {}"
| "assigned (v ::= va) = {v}"
| "assigned (v;; va) = assigned v \<union> assigned va"
| "assigned (IF v THEN va ELSE vb) = assigned va \<union> assigned vb"
| "assigned (WHILE v DO va) = assigned va"
| "assigned (REPEAT v UNTIL va) = assigned v"
| "assigned (p OR q) = assigned p \<union> assigned q"

lemma "\<lbrakk> (c, s) \<Rightarrow> t; x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = t x"
  apply (induct rule: big_step_induct)
  by auto

fun skip :: "com \<Rightarrow> bool" where
"skip SKIP = True"
| "skip (v ::= va) = (\<forall>s. s v = aval va s)"
| "skip (v;; va) = (skip v \<and> skip va)"
| "skip (IF v THEN va ELSE vb) = (skip va \<and> skip vb)"
| "skip (WHILE v DO va) = (\<forall>s. \<not>bval v s)"
| "skip (REPEAT v UNTIL va) = (skip v \<and> (\<forall>s. bval va s))"
| "skip (p OR q) = (skip p \<and> skip q)"

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
  apply (induct c rule: skip.induct; clarsimp)
  using assign_simp apply auto[1]
  apply fastforce
  apply (metis Chap7_2.IfE big_step.IfFalse big_step.IfTrue)
  by auto

lemma skip_while_aux: "\<lbrakk> (WHILE b DO c, s) \<Rightarrow> s'; bval b s \<rbrakk> \<Longrightarrow> \<not>bval b s'"
  apply (induct "WHILE b DO c" s s' rule: big_step_induct)
  by blast+

lemma skip_while: "bval b s \<Longrightarrow> \<not>(WHILE b DO c \<sim> SKIP)"
text \<open>if the loop halts after n iterations, then @{term "(WHILE b DO c, s) \<Rightarrow> sn"} and since
@{term "bval b s \<noteq> bval b sn"}, @{term "s \<noteq> sn"}. otherwise, the loop never halts,
so for all t, @{term "(WHILE b DO c, s) \<Rightarrow> t"} does not hold.\<close>
  using skip_while_aux by blast

lemma "WHILE b DO c \<sim> SKIP = skip (WHILE b DO c)"
  by (metis Chap7_2.SkipE Chap7_2.WhileE Skip WhileFalse skip.simps(5) skip_while_aux)

lemma "x ::= (V x) \<sim> SKIP"
  using assign_simp by auto

lemma "SKIP;; x ::= (V x) \<sim> SKIP"
  using assign_simp by auto

lemma
"let c1 = SKIP in
let c2 = x ::= Plus (V x) (N 1) in
IF (Bc True) THEN c1 ELSE c2 \<sim> SKIP"
  apply clarsimp
  by (metis Chap7_2.IfE big_step.IfTrue bval.simps(1))

lemma "c \<sim> SKIP \<Longrightarrow> skip c"
  apply (induction c)
      apply simp_all
     apply (metis Chap7_2.SkipE big_step.Assign fun_upd_idem_iff)
  oops

fun skip' :: "com \<Rightarrow> bool" where
"skip' SKIP = True"
| "skip' (v ::= va) = False"
| "skip' (v;; va) = (skip' v \<and> skip' va)"
| "skip' (IF v THEN va ELSE vb) = (skip' va \<and> skip' vb)"
| "skip' (WHILE v DO va) = False"
| "skip' (REPEAT v UNTIL va) = False"
| "skip' (p OR q) = (skip' p \<and> skip' q)"

lemma "skip' c \<Longrightarrow> c \<sim> SKIP"
  apply (induct c rule: skip'.induct; clarsimp)
    apply fastforce
  apply (metis Chap7_2.IfE big_step.IfFalse big_step.IfTrue)
  by blast

fun deskip :: "com \<Rightarrow> com" where
"deskip SKIP = SKIP"
| "deskip (v ::= a) = v ::= a"
| "deskip (SKIP;; p) = deskip p"
| "deskip (p;; SKIP) = deskip p"
| "deskip (p;; q) = (let (p', q') = (deskip p, deskip q) in
if p' = SKIP then q' else if q' = SKIP then p' else p';;q')"
| "deskip (IF b THEN p ELSE q) = IF b THEN deskip p ELSE deskip q"
| "deskip (WHILE b DO p) = WHILE b DO deskip p"
| "deskip (REPEAT p UNTIL b) = REPEAT deskip p UNTIL b"
| "deskip (p OR q) = deskip p OR deskip q"

lemma "deskip (SKIP ;; WHILE b DO (x ::= a;; SKIP)) = WHILE b DO x ::= a"
  by simp

lemma "deskip ((SKIP;; SKIP);; (SKIP;; SKIP)) = SKIP"
  by simp

lemma sim_rep_cong_aux: "(REPEAT c UNTIL b, s) \<Rightarrow> t \<Longrightarrow> c \<sim> c' \<Longrightarrow> (REPEAT c' UNTIL b, s) \<Rightarrow> t"
  by (induct "REPEAT c UNTIL b" s t rule: big_step_induct; auto)

lemma "deskip c \<sim> c"
  apply (induction c rule: deskip.induct; clarsimp)
                      apply (blast+)[7]
                      apply (case_tac "deskip (vb;; vc) = SKIP"; simp)
                      apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                      apply (blast+)[5]
                      apply (case_tac "deskip (v;; va) = SKIP"; simp)
                      apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                      apply blast
                      apply (case_tac "deskip (vb;; vc) = SKIP"; case_tac "deskip (v;; va) = SKIP"; simp)
                      apply (metis (full_types) Chap7_2.SeqE Chap7_2.SkipE Seq)
                      apply ((metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)+)[2]
                      apply blast
                      apply ( case_tac "deskip (v;; va) = SKIP"; simp)
                      apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                      apply blast
                      apply (case_tac "deskip (v;; va) = SKIP"; simp)
                      apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                      apply (meson Chap7_2.SeqE Seq)
                      apply (case_tac "deskip (v;; va) = SKIP"; simp)
                      apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                      apply blast
                      apply (case_tac "deskip (v;; va) = SKIP"; simp)
                      apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                      apply blast
                      apply (meson Chap7_2.SeqE Seq)
                      apply (case_tac "deskip (vc;; vd) = SKIP"; simp)
                      apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                      apply ((meson Chap7_2.SeqE Seq)+)[6]
                      apply (case_tac "deskip (vb;; vc) = SKIP"; simp)
                      apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                      apply ((meson Chap7_2.SeqE Seq)+)[6]
                apply (case_tac "deskip (vb;; vc) = SKIP"; simp)
                 apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
                apply ((meson Chap7_2.SeqE Seq)+)[6]
          apply (case_tac "deskip (vb;; vc) = SKIP"; simp)
           apply (metis Chap7_2.SeqE Chap7_2.SkipE Seq Skip)
          apply ((meson Chap7_2.SeqE Seq)+)[6]
      apply (blast+)[2]
    apply (simp add: sim_while_cong)
   apply (meson sim_rep_cong_aux)
  by blast

inductive astep :: "aexp * state \<Rightarrow> aexp \<Rightarrow> bool" (infix "\<leadsto>" 50) where
"(V x, s) \<leadsto> N (s x)"
| "(Plus (N i) (N j), s) \<leadsto> N (i + j)"
| "(e, s) \<leadsto> e' \<Longrightarrow> (Plus e e'', s) \<leadsto> Plus e' e''"
| "(e, s) \<leadsto> e' \<Longrightarrow> (Plus (N i) e, s) \<leadsto> Plus (N i) e'"

lemma "(a, s) \<leadsto> a' \<Longrightarrow> aval a s = aval a' s"
  thm astep.induct astep.induct[split_format (complete)]
proof (induction rule: astep.induct[split_format (complete)])
  fix x s
  show "aval (V x) s = aval (N (s x)) s" by simp
next
  fix i j s
  show "aval (Plus (N i) (N j)) s = aval (N (i + j)) s" by simp
next
  fix e s e' e''
  assume "(e, s) \<leadsto> e'" and "aval e s = aval e' s"
  thus "aval (Plus e e'') s = aval (Plus e' e'') s" by simp
next
  fix e s e' i
  assume "(e, s) \<leadsto> e'" and "aval e s = aval e' s"
  thus "aval (Plus (N i) e) s = aval (Plus (N i) e') s" by simp
qed

lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN (IF b2 THEN c1 ELSE c2) ELSE c2"
  apply clarsimp
  subgoal for s t
    apply (cases "bval b1 s")
    by fastforce+
  done

lemma helper_7_5: "\<not>(WHILE Bc True DO c, s) \<Rightarrow> t"
  apply clarsimp
  by (induct "WHILE Bc True DO c" s t rule: big_step_induct; simp)

lemma "\<not>WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"
  if "b1 \<equiv> Eq (N 0) (V ''x'')" and "b2 \<equiv> Bc True" and "c \<equiv> ''x'' ::= Plus (V ''x'') (N 1)"
and "s \<equiv> (\<lambda>_. 0) :: char list \<Rightarrow> int" and "t \<equiv> <''x'' := 1::int>"
  apply clarsimp
  apply (rule exI[where x=s])
  apply (rule exI[where x=t])
  apply (subgoal_tac "(WHILE And b1 b2 DO c, s) \<Rightarrow> t")
   apply (subgoal_tac "\<not> (WHILE b1 DO WHILE b2 DO c, s) \<Rightarrow> t")
    apply simp
   apply (thin_tac "_")
   apply clarsimp
   apply (erule Chap7_2.WhileE)
  defer
  unfolding that apply simp
   apply (rule WhileTrue[where t=t])
     apply simp
    apply (subgoal_tac "t = (\<lambda>_. 0)(''x'' := 1)")
  apply (simp add: assign_simp)
  unfolding that(5)
    apply (simp add: null_state_def)
   apply (rule WhileFalse; simp)
  using helper_7_5 by blast

abbreviation Or where "Or b1 b2 \<equiv> Not (And (Not b1) (Not b2))"

lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c;; WHILE b1 DO c"
  apply clarsimp
  subgoal for s t
  apply (rule iffI)
     apply (induct "WHILE Or b1 b2 DO c" s t rule: big_step_induct; clarsimp)
      apply (metis Seq WhileTrue bval.simps(2) bval.simps(3))
    apply (metis Seq WhileFalse bval.simps(2) bval.simps(3))
    by (metis Chap7_2.SeqE Chap7_2.WhileE bval.simps(2) bval.simps(3) skip_while_aux)
  done

definition DoWhile :: "com \<Rightarrow> bexp \<Rightarrow> com" ("(DO _ WHILE _)")where
"DO c WHILE b \<equiv> c ;; WHILE b DO c"

fun dewhile :: "com \<Rightarrow> com" where
"dewhile SKIP = SKIP"
| "dewhile (x ::= a) = x ::= a"
| "dewhile (p ;; q) = dewhile p ;; dewhile q"
| "dewhile (IF b THEN p ELSE q) = IF b THEN (dewhile p) ELSE (dewhile q)"
| "dewhile (WHILE b DO c) = IF (Not b) THEN SKIP ELSE DO c WHILE b"
| "dewhile (REPEAT c UNTIL b) = REPEAT dewhile c UNTIL b"
| "dewhile (p OR q) = dewhile p OR dewhile q"

lemma "dewhile c \<sim> c"
  apply (induct c)
  using DoWhile_def Seq Skip big_step.IfFalse big_step.IfTrue sim_rep_cong_aux by auto

end
