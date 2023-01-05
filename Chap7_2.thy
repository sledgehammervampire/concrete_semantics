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

value "''x'' ::= Plus (V ''y'') (N 1) ;; ''y'' ::= N 2"

inductive big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55) where
Skip: "(SKIP, s) \<Rightarrow> s"
| Assign: "(x ::= a, s) \<Rightarrow> s(x := aval a s)"
| Seq: "\<lbrakk> (c1, s1) \<Rightarrow> s2; (c2, s2) \<Rightarrow> s3 \<rbrakk> \<Longrightarrow> (c1 ;; c2, s1) \<Rightarrow> s3"
| IfTrue: "\<lbrakk> bval b s; (c1, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
| IfFalse: "\<lbrakk> \<not>bval b s; (c2, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (IF b THEN c1 ELSE c2, s) \<Rightarrow> t"
| WhileTrue: "\<lbrakk> bval b s; (c, s) \<Rightarrow> t; (WHILE b DO c, t) \<Rightarrow> u \<rbrakk> \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> u"
| WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c, s) \<Rightarrow> s"
| RepeatTrue: "\<lbrakk> bval b t; (c, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> t"
| RepeatFalse: "\<lbrakk> \<not>bval b t; (c, s) \<Rightarrow> t; (REPEAT c UNTIL b, t) \<Rightarrow> u \<rbrakk> \<Longrightarrow> (REPEAT c UNTIL b, s) \<Rightarrow> u"
| ChoiceLeft: "(c, s) \<Rightarrow> t \<Longrightarrow> (c OR c', s) \<Rightarrow> t"
| ChoiceRight: "(c', s) \<Rightarrow> t \<Longrightarrow> (c OR c', s) \<Rightarrow> t"

schematic_goal ex: "(''x'' ::= N 5;; '' y'' ::= V ''x'', s) \<Rightarrow> ?t"
  apply (rule Seq)
   apply (rule Assign)
  apply simp
  apply (rule Assign)
  done

thm ex[simplified]

code_pred big_step .

values "{t. (SKIP, \<lambda>_. 0) \<Rightarrow> t}"
values "{map t [''x'', ''y''] | t. (''x'' ::= N 2, \<lambda>_. 0) \<Rightarrow> t}"
values "{map t [''x''] |t. (SKIP, <''x'' := 42>) \<Rightarrow> t}"
values "{map t [''x''] |t. (''x'' ::= N 2, <''x'' := 42>) \<Rightarrow> t}"
values "{map t [''x'',''y''] |t.
  (WHILE Less (V ''x'') (V ''y'') DO (''x'' ::= Plus (V ''x'') (N 5)),
   <''x'' := 0, ''y'' := 13>) \<Rightarrow> t}"

declare big_step.intros [intro]

thm big_step.induct
lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive_cases SkipE[elim!]: "(SKIP, s) \<Rightarrow> t"
thm SkipE
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

lemma assign_simp:
"(x ::= a, s) \<Rightarrow> t \<longleftrightarrow> t = s(x := aval a s)"
  by blast

lemma seq_assoc:
"((c1;; c2);; c3, s) \<Rightarrow> t \<longleftrightarrow> (c1;; (c2;; c3), s) \<Rightarrow> t"
proof
  assume a1: "(c1;; c2;; c3, s) \<Rightarrow> t"
  thm SeqE[OF a1]
  obtain s1 where f1: "(c1 ;; c2, s) \<Rightarrow> s1" and f2: "(c3, s1) \<Rightarrow> t" by (elim SeqE[OF a1])
  obtain s2 where f3: "(c1, s) \<Rightarrow> s2" and f4: "(c2, s2) \<Rightarrow> s1" by (elim SeqE[OF f1])
  have f5: "(c2;; c3, s2) \<Rightarrow> t" by (intro Seq[OF f4 f2])
  show "(c1;; (c2;; c3), s) \<Rightarrow> t" by (intro Seq[OF f3 f5])
next
  assume "(c1;; (c2;; c3), s) \<Rightarrow> t"
  thus "(c1;; c2;; c3, s) \<Rightarrow> t" by blast
qed

abbreviation equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
"c \<sim> c' \<equiv> (\<forall>s t. (c, s) \<Rightarrow> t = (c', s) \<Rightarrow> t)"

lemma "WHILE b DO c \<sim> IF b THEN c;; WHILE b DO c ELSE SKIP"
  by blast

lemma "c \<sim> IF b THEN c ELSE c" by blast

lemma sim_while_cong_aux: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> c \<sim> c' \<Longrightarrow> (WHILE b DO c', s) \<Rightarrow> t"
  by (induct "WHILE b DO c" s t rule: big_step_induct; auto)

lemma sim_while_cong: "c \<sim> c' \<Longrightarrow> WHILE b DO c \<sim> WHILE b DO c'"
  using sim_while_cong_aux by meson

end