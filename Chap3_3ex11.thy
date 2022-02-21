theory Chap3_3ex11
imports Main Chap3_1 Chap3_2
begin

type_synonym reg = nat
type_synonym reg_state = "nat \<Rightarrow> int"

datatype instr = LDI int reg | LD vname reg | ADD reg reg

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" where
"exec1 (LDI n r) _ rs = rs(r := n)"
| "exec1 (LD x r) s rs = rs(r := s x)"
| "exec1 (ADD r1 r2) _ rs = rs(r1 := rs r1 + rs r2)"

definition exec :: "instr list \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" where
"exec is s = fold (\<lambda>i. exec1 i s) is"

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
"comp (N n) r = [LDI n r]"
| "comp (V x) r = [LD x r]"
| "comp (Plus e1 e2) r = comp e1 r @ comp e2 (r + 1) @ [ADD r (r+1)]"

lemma comp_no_clobber:
"r' < r \<Longrightarrow> exec (comp a1 r) s rs r' = rs r'"
  apply (induction a1 r arbitrary: rs rule: comp.induct)
  unfolding exec_def by simp+

lemma "exec (comp a r) s rs r = aval a s"
  apply (induction a arbitrary: r rs)
  unfolding exec_def using comp_no_clobber exec_def
  by auto

end