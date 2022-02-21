theory Chap3_3ex12
imports Main Chap3_1 Chap3_2
begin

type_synonym reg = nat
type_synonym reg_state = "nat \<Rightarrow> int"

datatype instr0 = LDI0 val | LD0 vname | MV0 reg | ADD0 reg

fun exec1 :: "instr0 \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" where
"exec1 (LDI0 n) _ rs = rs(0 := n)"
| "exec1 (LD0 x) s rs = rs(0 := s x)"
| "exec1 (MV0 r) _ rs = rs(r := rs 0)"
| "exec1 (ADD0 r) _ rs = rs(0 := rs 0 + rs r)"

definition exec :: "instr0 list \<Rightarrow> state \<Rightarrow> reg_state \<Rightarrow> reg_state" where
"exec is s = fold (\<lambda>i. exec1 i s) is"

fun comp :: "aexp \<Rightarrow> reg \<Rightarrow> instr0 list" where
"comp (N n) r = [LDI0 n, MV0 r]"
| "comp (V x) r = [LD0 x, MV0 r]"
| "comp (Plus e1 e2) r = comp e1 (r+1) @ comp e2 (r+2) @ [LDI0 0, ADD0 (r+1), ADD0 (r+2), MV0 r]"

lemma comp_no_clobber:
"\<lbrakk> 0 < r' \<and> r' < r \<rbrakk> \<Longrightarrow> exec (comp a r) s rs r' = rs r'"
  apply (induction a r arbitrary: rs rule: comp.induct)
  unfolding exec_def by simp+
 
lemma "exec (comp a r) s rs r = aval a s \<and> exec (comp a r) s rs 0 = aval a s"
  apply (induction a r arbitrary: rs rule: comp.induct)
  unfolding exec_def using comp_no_clobber exec_def by auto

end