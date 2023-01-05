theory Chap7_3
  imports
Main
Chap7_2
"HOL-IMP.Star"
begin

inductive small_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>" 55) where
Assign: "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))"
| Seq1: "(SKIP ;; p, s) \<rightarrow> (p, s)"
| Seq2: "(p, s) \<rightarrow> (p', s') \<Longrightarrow> (p ;; q, s) \<rightarrow> (p' ;; q, s')"
| IfTrue: "bval b s \<Longrightarrow> (IF b THEN p ELSE q, s) \<rightarrow> (p, s)"
| IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN p ELSE q, s) \<rightarrow> (q, s)"
| While: "(WHILE b DO p, s) \<rightarrow> (IF b THEN p ;; WHILE b DO p ELSE SKIP, s)"
| Repeat: "(REPEAT p UNTIL b, s) \<rightarrow> (p ;; IF b THEN SKIP ELSE REPEAT p UNTIL b, s)"
| ChoiceLeft: "(p OR q, s) \<rightarrow> (p, s)"
| ChoiceRight: "(p OR q, s) \<rightarrow> (q, s)"

code_pred small_step .

abbreviation small_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y \<equiv> star small_step x y"

values "{(c', map t [''x'', ''y'', ''z'']) | c' t.
(''x'' ::= V ''z'' ;; ''y'' ::= V ''x'', <''x'' := 3, ''y'' := 7, ''z'' := 5>) \<rightarrow>* (c', t)}"

values "{(c', map t [''x'', ''y'']) | c' t.
(IF Less (V ''x'') (N 4) THEN ''y'' ::= N 0 ELSE SKIP, <''x'' := 3, ''y'' := 7>) \<rightarrow>* (c', t)}"

values "{(c', map t [''x'']) | c' t.
(WHILE Less (V ''x'') (N 3) DO ''x'' ::= Plus (V ''x'') (N 1), <''x'' := 0>) \<rightarrow>* (c', t)}"

inductive_cases SkipE[elim!]: "(SKIP, s) \<rightarrow> cs"
thm SkipE
inductive_cases AssignE[elim!]: "(x ::= a, s) \<rightarrow> cs"
thm AssignE
inductive_cases SeqE[elim]: "(p ;; q, s) \<rightarrow> cs"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2, s) \<rightarrow> cs"
thm IfE
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<rightarrow> cs"
thm WhileE
inductive_cases RepeatE[elim]: "(REPEAT c UNTIL b, s) \<rightarrow> cs"
thm RepeatE
inductive_cases ChoiceE[elim!]: "(p OR q, s) \<rightarrow> cs"
thm ChoiceE

lemma "\<lbrakk> (p, s) \<rightarrow>* (SKIP, s'); (p', s') \<rightarrow>* cs \<rbrakk> \<Longrightarrow> (p ;; p', s) \<rightarrow>* cs"
  apply (induct p s SKIP s' rule: star_induct)
  apply (rule_tac y="(p', b)" in star.step)
  using Seq1 apply blast
   apply assumption
  apply (rule_tac y="(aa;;p', ba)" in star.step)
  using Seq2 apply blast
  by simp

lemma bs_ref_ss_aux: "\<lbrakk> (p, s) \<rightarrow>* (SKIP, s'); (p', s') \<rightarrow>* cs \<rbrakk> \<Longrightarrow> (p ;; p', s) \<rightarrow>* cs"
  apply (induct p s SKIP s' rule: star_induct)
  by (meson small_step.intros star.step)+

lemma "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
  apply (induct rule: big_step.induct)
  apply simp
  using small_step.Assign apply blast
  using bs_ref_ss_aux apply blast
  apply (meson small_step.IfTrue star.step)
  apply (meson small_step.IfFalse star.simps)
  apply (meson While bs_ref_ss_aux small_step.IfTrue star.step)
      apply (meson While small_step.IfFalse star.step star_step1)
  subgoal for b t c s
   apply (rule star.step[where y="(c;; IF b THEN SKIP ELSE REPEAT c UNTIL b, s)"])
    using Repeat apply blast
    by (simp add: bs_ref_ss_aux small_step.IfTrue)
  apply (meson Repeat bs_ref_ss_aux small_step.IfFalse star.step)
  apply (meson small_step.ChoiceLeft star.step)
  by (meson small_step.ChoiceRight star.step)

lemma bs_ref_ss: "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP, t)"
proof (induct rule: big_step.induct)
  case Seq
  thus ?case using bs_ref_ss_aux by blast
next
  case WhileTrue
  thus ?case by (meson bs_ref_ss_aux While small_step.IfTrue star.step)
next
  case RepeatFalse
  thus ?case by (meson Repeat bs_ref_ss_aux small_step.IfFalse star.step)
next
  case RepeatTrue
  thus ?case by (meson Repeat bs_ref_ss_aux small_step.IfTrue star.step star_step1)
qed (meson small_step.intros star.intros)+

lemma "x \<rightarrow> y \<Longrightarrow> y \<rightarrow>* (SKIP, t) \<Longrightarrow> y \<Rightarrow> t \<Longrightarrow> x \<Rightarrow> t"
proof (induct arbitrary: t rule: small_step.induct)
  case (Seq2 p s p' s' q)
  then show ?case
    apply (elim Chap7_2.SeqE)
    apply (frule bs_ref_ss)
    apply (rule_tac ?s2.0="s2" in Seq)
    by assumption
next
  case While
  then show ?case
    apply (elim Chap7_2.IfE)
    apply (elim Chap7_2.SeqE)
    by blast+
qed blast+

lemma ss_ref_bs_aux: "x \<rightarrow> y \<Longrightarrow> y \<rightarrow>* (SKIP, t) \<Longrightarrow> y \<Rightarrow> t \<Longrightarrow> x \<Rightarrow> t"
proof (induct arbitrary: t rule: small_step.induct)
  case Seq2
  thus ?case using bs_ref_ss by auto
qed blast+

lemma ss_ref_bs: "cs \<rightarrow>* (SKIP, t) \<Longrightarrow> cs \<Rightarrow> t"
  apply (induct cs "(SKIP, t)" rule: star.induct)
  using ss_ref_bs_aux by auto

lemma "cs \<rightarrow>* (SKIP, t) = cs \<Rightarrow> t"
  by (metis ss_ref_bs bs_ref_ss)

definition final :: "com * state \<Rightarrow> bool" where
"final cs \<equiv> \<not>(\<exists>cs'. cs \<rightarrow> cs')"

lemma final_iff_SKIP: "final (c, s) = (c = SKIP)"
  apply (induction c)
  unfolding final_def apply blast
  using small_step.Assign apply blast
  apply (metis Seq1 Seq2 com.distinct(3) old.prod.exhaust)
  apply (metis com.distinct(5) small_step.IfFalse small_step.IfTrue)
  using While apply blast
  using Repeat apply blast
  using small_step.ChoiceLeft by blast

lemma "(\<exists>t. cs \<Rightarrow> t) = (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"
  by (metis bs_ref_ss final_iff_SKIP ss_ref_bs surj_pair)

end