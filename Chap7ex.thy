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
| "assigned THROW = {}"
| "assigned (TRY p CATCH c) = assigned p \<union> assigned c"

lemma "\<lbrakk> (c, s) \<Rightarrow> (r, s'); x \<notin> assigned c \<rbrakk> \<Longrightarrow> s x = s' x"
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
| "skip THROW = False"
| "skip (TRY p CATCH c) = (skip p \<and> skip c)"

lemma "skip c \<Longrightarrow> c \<sim> SKIP"
  apply (induct c rule: skip.induct; clarsimp)
  using assign_simp apply auto[1]
  apply fastforce
  apply (metis Chap7_2.IfE big_step.IfFalse big_step.IfTrue)
  by blast+

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
         apply (metis Skip assign_simp fun_upd_idem_iff)
  oops

fun skip' :: "com \<Rightarrow> bool" where
"skip' SKIP = True"
| "skip' (v ::= va) = False"
| "skip' (v;; va) = (skip' v \<and> skip' va)"
| "skip' (IF v THEN va ELSE vb) = (skip' va \<and> skip' vb)"
| "skip' (WHILE v DO va) = False"
| "skip' (REPEAT v UNTIL va) = False"
| "skip' (p OR q) = (skip' p \<and> skip' q)"
| "skip' THROW = False"
| "skip' (TRY p CATCH c) = (skip' p \<and> skip' c)"

lemma "skip' c \<Longrightarrow> c \<sim> SKIP"
  apply (induct c rule: skip'.induct; clarsimp)
     apply fastforce
    apply (metis Chap7_2.IfE big_step.IfFalse big_step.IfTrue)
   apply (metis Chap7_2.ChoiceE big_step.ChoiceRight)
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
| "deskip THROW = THROW"
| "deskip (TRY p CATCH c) = TRY (deskip p) CATCH (deskip c)"

lemma "deskip (SKIP ;; WHILE b DO (x ::= a;; SKIP)) = WHILE b DO x ::= a"
  by simp

lemma "deskip ((SKIP;; SKIP);; (SKIP;; SKIP)) = SKIP"
  by simp

lemma skipr[simp]: "(p;;SKIP, s) \<Rightarrow> cs = (p, s) \<Rightarrow> cs"
  by (smt (verit, del_insts) Chap7_2.SeqE Chap7_2.SkipE Seq SeqThrow bs_ref_ss final_iff_SKIP old.prod.exhaust ss_ref_bs star.simps)

lemma skipl[simp]: "(SKIP;;p, s) \<Rightarrow> cs = (p, s) \<Rightarrow> cs"
  by blast

lemma "deskip c \<sim> c"
  apply (induction c rule: deskip.induct; clarsimp)
                      apply (smt (verit, del_insts) Chap7_2.SeqE Seq SeqThrow Skip final_iff_SKIP ss_eq_bs Chap7_2.SkipE)
                      apply blast
                      apply auto[2]
                      apply blast
                      apply blast
                      apply (smt (verit) Chap7_2.SeqE Chap7_2.SkipE Pair_inject Seq SeqThrow Skip com.distinct(13))
                      apply (case_tac "deskip (vb;; vc) = SKIP"; case_tac "deskip (v;; va) = SKIP"; clarsimp)
                      apply (smt (verit) Chap7_2.SeqE Chap7_2.SkipE Seq)
                      apply (smt (verit, ccfv_threshold) Chap7_2.SeqE Chap7_2.SkipE Seq SeqThrow final_iff_SKIP ss_eq_bs star.simps)
                      apply (smt (verit) Chap7_2.SeqE Chap7_2.SkipE Seq Skip com.distinct(13) old.prod.inject)
                      apply blast
                      apply (smt (verit) Chap7_2.SeqE Chap7_2.SkipE Pair_inject Seq SeqThrow Skip com.distinct(13))
                      apply (smt (verit, ccfv_SIG) Chap7_2.SeqE Chap7_2.SkipE Seq SeqThrow Skip com.distinct(13) old.prod.inject)
                      apply (smt (verit, ccfv_SIG) Chap7_2.SeqE Chap7_2.SkipE Pair_inject Seq SeqThrow Skip com.distinct(13))
                      apply (smt (verit, del_insts) Chap7_2.SeqE Seq SeqThrow skipl)
                      apply (smt (verit, best) Chap7_2.SeqE Chap7_2.SkipE Seq SeqThrow Skip prod.inject)
                      apply (case_tac "deskip (v;; va) = SKIP"; clarsimp)
                      apply (smt (verit, best) Chap7_2.SeqE Seq SeqThrow Skip skipl)
                      apply (smt (verit, best) Chap7_2.SeqE Seq SeqThrow Skip skipl)
                      apply blast
                      apply (smt (verit, ccfv_threshold) Chap7_2.SeqE Chap7_2.SkipE Seq SeqThrow Skip bs_ref_ss final_iff_SKIP)
                      apply blast
                      apply (smt (verit, ccfv_SIG) Chap7_2.SeqE Seq SeqThrow)
  using SeqThrow apply (blast+)[4]
                      apply auto[1]
                      apply (smt (verit) Chap7_2.SeqE Chap7_2.SkipE Seq SeqThrow Skip final_iff_SKIP ss_eq_bs)
                      apply (smt (verit, del_insts) Chap7_2.SeqE Seq SeqThrow)
                      apply auto[2]
                      apply (smt (verit) Chap7_2.SeqE Seq SeqThrow)
                      apply auto[1]
                      apply (smt (verit, ccfv_SIG) Chap7_2.SeqE Seq SeqThrow)
                      apply auto[1]
                      apply (smt (verit, ccfv_threshold) Chap7_2.SeqE Chap7_2.SkipE Seq SeqThrow Skip final_iff_SKIP ss_eq_bs)
                      apply blast
                      apply auto[2]
  using SeqThrow apply (blast+)[4]
                      apply (smt (verit, best) Chap7_2.SeqE Chap7_2.SkipE Seq SeqThrow Skip final_iff_SKIP ss_eq_bs)
                      apply blast
                      apply (smt (verit, ccfv_SIG) Chap7_2.SeqE Seq SeqThrow)
  using Seq SeqThrow apply (blast+)[11]
             apply (case_tac "deskip (vb;; vc) = SKIP"; clarsimp)
              apply (smt (verit) Chap7_2.SeqE Seq SeqThrow skipr)
             apply blast
  using SeqThrow apply blast
           apply (smt (verit, best) Chap7_2.SeqE Seq SeqThrow)
  using SeqThrow apply (blast+)[5]
  using sim_while_cong_aux apply fastforce
  using sim_rep_cong_aux apply fastforce
  by blast+

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

lemma "\<not>WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"
  if "b1 \<equiv> Eq (N 0) (V ''x'')" and "b2 \<equiv> Bc True" and "c \<equiv> ''x'' ::= Plus (V ''x'') (N 1)"
and "s \<equiv> <> :: (char list \<Rightarrow> int)" and "t \<equiv> <''x'' := 1::int>"
  apply clarsimp
  apply (rule exI[where x=s])
  apply (rule exI[where x=SKIP])
  apply (rule exI[where x=t])
  apply (subgoal_tac "(WHILE And b1 b2 DO c, s) \<Rightarrow> (SKIP, t)" "(WHILE b1 DO WHILE b2 DO c, s) \<Rightarrow> (SKIP, t) \<Longrightarrow> False")
  apply blast
   apply (thin_tac "_")
   apply (erule Chap7_2.WhileE)
     apply (thin_tac "_")
     apply (thin_tac "_ \<Rightarrow> (SKIP, t)")
  subgoal for t
    apply (induct "WHILE b2 DO c" s SKIP t rule: big_step_induct)
    unfolding that(2) by auto
  apply simp
   apply (simp add: fun_upd_idem_iff null_state_def that(4) that(5))
  apply (rule WhileTrue[where t=t])
    apply (simp add: null_state_def that(1) that(2) that(4))
  apply (subgoal_tac "t = s(''x'' := aval (Plus (V ''x'') (N 1)) s)")
  using that(3) apply blast
  apply (simp add: null_state_def that(4) that(5))
  apply (rule WhileFalse)
  by (simp add: that(1) that(5))

abbreviation Or where "Or b1 b2 \<equiv> Not (And (Not b1) (Not b2))"

lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c;; WHILE b1 DO c"
  apply clarsimp
  subgoal for s t b
    apply (rule iffI)
     apply (induct "WHILE Or b1 b2 DO c" s t b rule: big_step_induct; clarsimp)
       apply (smt (verit, ccfv_SIG) Chap7_2.SeqE Seq SeqThrow WhileTrue bval.simps(2) bval.simps(3))
      apply (simp add: SeqThrow WhileTrueThrow)
     apply (metis Seq WhileFalse bval.simps(2) bval.simps(3))
    apply (erule Chap7_2.SeqE)
    subgoal for s2
      apply (induct "WHILE Or b1 b2 DO c" s SKIP s2 rule: big_step_induct; clarsimp)
      using WhileTrue bval.simps(2) bval.simps(3) apply presburger
      using WhileFalse by auto
    by simp
  done

definition DoWhile :: "com \<Rightarrow> bexp \<Rightarrow> com" ("(DO _ WHILE _)")where
"DO c WHILE b \<equiv> c ;; WHILE b DO c"

fun dewhile :: "com \<Rightarrow> com" where
"dewhile SKIP = SKIP"
| "dewhile (x ::= a) = x ::= a"
| "dewhile (p ;; q) = dewhile p ;; dewhile q"
| "dewhile (IF b THEN p ELSE q) = IF b THEN (dewhile p) ELSE (dewhile q)"
| "dewhile (WHILE b DO c) = IF (Not b) THEN SKIP ELSE DO (dewhile c) WHILE b"
| "dewhile (REPEAT c UNTIL b) = REPEAT dewhile c UNTIL b"
| "dewhile (p OR q) = dewhile p OR dewhile q"
| "dewhile THROW = THROW"
| "dewhile (TRY p CATCH c) = TRY (dewhile p) CATCH (dewhile c)"

lemma "dewhile c \<sim> c"
  apply (induct c; clarsimp)
       apply blast
      apply blast
  subgoal for b c s r t
    apply (rule iffI)
     apply (erule Chap7_2.IfE)
      apply auto[1]
    unfolding DoWhile_def apply (erule Chap7_2.SeqE)
      apply (simp add: WhileTrue sim_while_cong_aux)
     apply (simp add: WhileTrueThrow)
    apply (erule Chap7_2.WhileE)
      apply (rule Chap7_2.IfFalse)
    using bval.simps(2) apply blast
      apply (simp add: Seq sim_while_cong_aux)
     apply (simp add: SeqThrow big_step.IfFalse)
    by (simp add: Skip big_step.IfTrue)
    apply (simp add: sim_rep_cong)
  by blast+

end
