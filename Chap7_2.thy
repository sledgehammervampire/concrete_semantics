theory Chap7_2
  imports
Main
Chap3_1
Chap3_2
begin

datatype com = SKIP
  | Assign vname aexp ("_ ::= _" [1000, 61] 61)
  | Seq com com ("_;;/ _"  [60, 61] 60)
  | If bexp com com ("(IF _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
  | While bexp com ("(WHILE _/ DO _)"  [0, 61] 61)
  | Repeat com bexp ("(REPEAT _/ UNTIL _)")
  | Choice com com ("_ OR _" [60, 61] 60)
  | THROW
  | TryCatch com com ("(TRY _/ CATCH _)")

value "''x'' ::= Plus (V ''y'') (N 1) ;; ''y'' ::= N 2"

inductive big_step :: "com \<times> state \<Rightarrow> com \<times> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
Skip: "(SKIP, s) \<Rightarrow> (SKIP, s)"
| Throw: "(THROW, s) \<Rightarrow> (THROW, s)"
| Assign: "(x ::= a, s) \<Rightarrow> (SKIP, s(x := aval a s))"
| Seq: "\<lbrakk> (c1, s1) \<Rightarrow> (SKIP, s2); (c2, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1 ;; c2, s1) \<Rightarrow> s3"
| SeqThrow: "(c1, s1) \<Rightarrow> (THROW, s2) \<Longrightarrow> (c1;; c2, s1) \<Rightarrow> (THROW, s2)"
| IfTrue: "\<lbrakk> bval b s; (c1, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
| IfFalse: "\<lbrakk> \<not>bval b s; (c2, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
| WhileTrue: "\<lbrakk> bval b s; (c, s) \<Rightarrow> (SKIP, t); (WHILE b DO c, t) \<Rightarrow> u \<rbrakk> \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> u"
| WhileTrueThrow: "\<lbrakk> bval b s; (c, s) \<Rightarrow> (THROW, t) \<rbrakk> \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> (THROW, t)"
| WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> (SKIP, s)"
| RepeatTrue: "\<lbrakk> bval b t; (c, s) \<Rightarrow> (SKIP, t) \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> (SKIP, t)"
| RepeatFalse: "\<lbrakk> \<not>bval b t; (c, s) \<Rightarrow> (SKIP, t); (REPEAT c UNTIL b, t) \<Rightarrow> u \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> u"
| RepeatThrow: "\<lbrakk> (c, s) \<Rightarrow> (THROW, t) \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> (THROW, t)"
| ChoiceLeft: "(c, s) \<Rightarrow> t \<Longrightarrow> (c OR c', s) \<Rightarrow> t"
| ChoiceRight: "(c', s) \<Rightarrow> t \<Longrightarrow> (c OR c', s) \<Rightarrow> t"
| Try: "(p, s) \<Rightarrow> (SKIP, s') \<Longrightarrow> (TRY p CATCH c, s) \<Rightarrow> (SKIP, s')"
| Catch: "\<lbrakk> (c1, s1) \<Rightarrow> (THROW, s2); (c2, s2) \<Rightarrow> r' \<rbrakk> \<Longrightarrow> (TRY c1 CATCH c2, s1) \<Rightarrow> r'"

schematic_goal ex: "(''x'' ::= N 5;; '' y'' ::= V ''x'', s) \<Rightarrow> ?t"
  apply (rule Seq)
   apply (rule Assign)
  apply simp
  apply (rule Assign)
  done

thm ex[simplified]

code_pred big_step .

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"
values "{map (snd t) [''x'', ''y''] | t. (''x'' ::= N 2, \<lambda>_. 0) \<Rightarrow> t}"
values "{map (snd t) [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"
values "{map (snd t) [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> t}"
values "{map (snd t) [''x'',''y''] |t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> t}"

declare big_step.intros [intro]

thm big_step.induct
lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive_cases SkipE[elim!]: "(SKIP, s) \<Rightarrow> t"
thm SkipE
inductive_cases ThrowE[elim!]: "(THROW, s) \<Rightarrow> t"
thm ThrowE
inductive_cases AssignE[elim!]: "(x ::= a, s) \<Rightarrow> t"
thm AssignE
inductive_cases SeqE[elim!]: "(c1 ;; c2, s1) \<Rightarrow> s3"
thm SeqE
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
thm IfE
inductive_cases WhileE[elim]: "(WHILE b DO c, s) \<Rightarrow> u"
thm WhileE
text \<open>only [elim]: [elim!] would not terminate\<close>
inductive_cases RepeatE[elim]: "(REPEAT c UNTIL b, s) \<Rightarrow> u"
thm RepeatE
inductive_cases ChoiceE[elim!]: "(p OR q, s) \<Rightarrow> t"
thm ChoiceE
inductive_cases TryCatchE[elim!]: "(TRY p CATCH c, s) \<Rightarrow> t"
thm TryCatchE

lemma assign_simp:
"(x ::= a, s) \<Rightarrow> (SKIP, t) \<longleftrightarrow> t = s(x := aval a s)"
  by blast

lemma seq_assoc:
"((c1;; c2);; c3, s) \<Rightarrow> t \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> t"
  by blast

abbreviation equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
"c \<sim> c' \<equiv> (\<forall>s t. (c, s) \<Rightarrow> t = (c', s) \<Rightarrow> t)"

lemma "WHILE b DO c \<sim> IF b THEN c;; WHILE b DO c ELSE SKIP"
  by blast

lemma "c \<sim> IF b THEN c ELSE c" by blast

lemma sim_while_cong_aux: "(WHILE b DO c, s) \<Rightarrow> (r, s') \<Longrightarrow> c \<sim> c' \<Longrightarrow> (WHILE b DO c', s) \<Rightarrow> (r, s')"
  by (induct "WHILE b DO c" s r s' rule: big_step_induct; auto)

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  using sim_while_cong_aux by (metis surj_pair)

lemma sim_rep_cong_aux: "(REPEAT c UNTIL b, s) \<Rightarrow> (r, s') \<Longrightarrow> c \<sim> c' \<Longrightarrow> (REPEAT c' UNTIL b, s) \<Rightarrow> (r, s')"
  by (induct "REPEAT c UNTIL b" s r s' rule: big_step_induct; auto)

lemma sim_rep_cong: "c \<sim> c' \<Longrightarrow> (REPEAT c UNTIL b) \<sim> REPEAT c' UNTIL b"
  using sim_rep_cong_aux by fastforce

fun is_det :: "com \<Rightarrow> bool" where
"is_det SKIP = True"
| "is_det (x ::= a) = True"
| "is_det (p ;; q) = (is_det p \<and> is_det q)"
| "is_det (IF b THEN p ELSE q) = (is_det p \<and> is_det q)"
| "is_det (WHILE b DO p) = is_det p"
| "is_det (REPEAT p UNTIL b) = is_det p"
| "is_det THROW = True"
| "is_det (TRY p CATCH q) = (is_det p \<and> is_det q)"
| "is_det (p OR q) = False"

lemma big_step_det: "\<lbrakk> (p, s) \<Rightarrow> t; (p, s) \<Rightarrow> t'; is_det p \<rbrakk> \<Longrightarrow> t = t'"
  apply (induct "(p, s)" t arbitrary: p s t' rule: big_step.induct)
                  apply (blast+)[3]
               apply (metis Pair_inject SeqE com.distinct(13) is_det.simps(3))
  using is_det.simps(3) apply blast
             apply (force, force)
           apply (metis Pair_inject WhileE com.distinct(13) is_det.simps(5))
          apply (metis WhileE com.distinct(13) is_det.simps(5) old.prod.inject)
         apply blast
        apply (metis (no_types, lifting) RepeatE is_det.simps(6) snd_conv)
       apply (smt (verit, best) RepeatE com.distinct(13) is_det.simps(6) prod.inject)
      apply (metis Pair_inject RepeatE com.simps(21) is_det.simps(6))
     apply auto[2]
  using is_det.simps(8) apply blast
  by (metis Pair_inject TryCatchE com.distinct(13) is_det.simps(8))

end
