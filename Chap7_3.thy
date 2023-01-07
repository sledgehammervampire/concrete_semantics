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
| TrySkip: "(TRY SKIP CATCH c, s) \<rightarrow> (SKIP, s)"
| Try: "(p, s) \<rightarrow> (p', s') \<Longrightarrow> (TRY p CATCH c, s) \<rightarrow> (TRY p' CATCH c, s')"
| Throw: "(THROW;; p, s) \<rightarrow> (THROW, s)"
| Catch: "(TRY THROW CATCH c, s) \<rightarrow> (c, s)"

code_pred small_step .

declare small_step.intros [intro]

abbreviation small_steps :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
  where "x \<rightarrow>* y \<equiv> star small_step x y"

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
inductive_cases ThrowE[elim!]: "(THROW, s) \<rightarrow> cs"
thm ThrowE
inductive_cases TryCatchE[elim]: "(TRY p CATCH c, s) \<rightarrow> cs"
thm TryCatchE

definition final :: "com * state \<Rightarrow> bool" where
"final cs \<equiv> \<not>(\<exists>cs'. cs \<rightarrow> cs')"

lemma final_iff_SKIP: "final (c, s) = (c = SKIP \<or> c = THROW)"
  apply (induct c)
  using final_def apply blast
  using final_def apply auto[1]
  apply (metis Seq1 Seq2 com.distinct(39) com.distinct(4) final_def small_step.Throw surj_pair)
  apply (metis com.distinct(49) com.distinct(5) final_def small_step.IfFalse small_step.IfTrue)
  apply (metis While com.distinct(57) com.distinct(7) final_def)
  apply (metis Repeat com.distinct(63) com.distinct(9) final_def)
  apply (metis com.distinct(11) com.distinct(67) final_def small_step.ChoiceRight)
  using final_def apply blast
  by (metis TrySkip com.distinct(15) com.distinct(71) final_def small_step.Catch small_step.Try surj_pair)

lemma bs_ref_ss_aux: "\<lbrakk> (c1, s1) \<rightarrow>* (SKIP, s2); (c2, s2) \<rightarrow>* cs \<rbrakk> \<Longrightarrow> (c1;; c2, s1) \<rightarrow>* cs"
  apply (induct c1 s1 SKIP s2 rule: star_induct)
   apply (meson Seq1 star.step)
  by (meson Seq2 star.step)

lemma bs_ref_ss_aux1: "(c1, s1) \<rightarrow>* (THROW, s2) \<Longrightarrow> (c1;; c2, s1) \<rightarrow>* (THROW, s2)"
  apply (induct c1 s1 THROW s2 rule: star_induct)
   apply (simp add: small_step.Throw)
  by (meson Seq2 star.step)

lemma bs_ref_ss_aux2: "(p, s) \<rightarrow>* (SKIP, s') \<Longrightarrow> (TRY p CATCH c, s) \<rightarrow>* (SKIP, s')"
  apply (induct p s SKIP s' rule: star_induct)
  apply (simp add: TrySkip)
  by (meson small_step.Try star.step)

lemma bs_ref_ss_aux3: "\<lbrakk> (c1, s1) \<rightarrow>* (THROW, s2); (c2, s2) \<rightarrow>* r'\<rbrakk> \<Longrightarrow> (TRY c1 CATCH c2, s1) \<rightarrow>* r'"
  apply (induct c1 s1 THROW s2 rule: star_induct)
  apply (meson small_step.Catch star.step)
  by (meson small_step.Try star.step)

lemma bs_ref_ss: "cs \<Rightarrow> cs' \<Longrightarrow> cs \<rightarrow>* cs' \<and> final cs'"
  unfolding final_def apply (induct rule: big_step.induct)
  apply blast+
  using bs_ref_ss_aux apply blast
  using bs_ref_ss_aux1 apply blast
             apply (meson small_step.IfTrue star.step)
            apply (metis small_step.IfFalse star.step)
           apply (meson While bs_ref_ss_aux small_step.IfTrue star.step)
          apply (meson While bs_ref_ss_aux1 small_step.IfTrue star.simps)
         apply (meson Chap7_3.SkipE While small_step.IfFalse star.step star_step1)
        apply (meson Repeat bs_ref_ss_aux small_step.IfTrue star.step star_step1)
       apply (meson Repeat bs_ref_ss_aux small_step.IfFalse star.step)
      apply (meson Repeat bs_ref_ss_aux1 star.step)
     apply (meson small_step.ChoiceLeft star.step)
    apply (meson small_step.ChoiceRight star.step)
  using bs_ref_ss_aux2 apply blast
  using bs_ref_ss_aux3 by blast

lemma ss_ref_bs_aux:
"\<lbrakk> cs \<rightarrow> cs'; cs' \<Rightarrow> cs''; final cs'' \<rbrakk> \<Longrightarrow> cs \<Rightarrow> cs''"
  unfolding final_def
proof (induct arbitrary: cs'' rule: small_step.induct)
  case Seq2
  thus ?case using bs_ref_ss by auto
qed blast+

lemma ss_ref_bs: "\<lbrakk> cs \<rightarrow>* cs'; final cs' \<rbrakk> \<Longrightarrow> cs \<Rightarrow> cs'"
  apply (induct cs cs' rule: star.induct)
  using final_iff_SKIP apply force
  using ss_ref_bs_aux by force

lemma ss_eq_bs: "final cs' \<and> cs \<rightarrow>* cs' \<longleftrightarrow> cs \<Rightarrow> cs'"
  by (metis ss_ref_bs bs_ref_ss)

lemma "(\<exists>t. cs \<Rightarrow> t) = (\<exists>cs'. cs \<rightarrow>* cs' \<and> final cs')"
  using ss_eq_bs by blast

end