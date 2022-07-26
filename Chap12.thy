theory Chap12 imports Main Chap7_2
begin

lemma helper:
assumes a1: "wsum = WHILE Less (N 0) (V ''x'') DO csum"
and a2: "csum = ''y'' ::= Plus (V ''y'') (V ''x'');; ''x'' ::= Plus (V ''x'') (N (-1))"
shows "(wsum, s) \<Rightarrow> t \<Longrightarrow> t ''y'' = s ''y'' + (\<Sum>i=0..s ''x''. i)"
proof (cases "s ''x''")
  let ?b = "Less (N 0) (V ''x'')"
  case (neg n)
  assume "(wsum, s) \<Rightarrow> t"
  hence "(WHILE ?b DO csum, s) \<Rightarrow> t" using a1 by simp
  moreover have "\<not>(bval ?b s)" using neg by simp
  ultimately have "s = t" using WhileE by blast
  moreover have "\<Sum>{0..s ''x''} = 0" using neg by simp
  ultimately show ?thesis by simp
next
  let ?b = "Less (N 0) (V ''x'')"
  case (nonneg n)
  assume "(wsum, s) \<Rightarrow> t"
  have "\<lbrakk> s ''x'' = int n; (wsum, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> t ''y'' = s ''y'' + \<Sum> {0..s ''x''}"
  proof (induct n arbitrary: s t)
    case 0
    hence "s = t" using a1 WhileE by auto
    with 0 show ?case by simp
  next
    case (Suc n)
    hence "bval ?b s" by simp
    moreover have "(WHILE ?b DO csum, s) \<Rightarrow> t" using a1 Suc by simp
    ultimately obtain u where f2: "(csum, s) \<Rightarrow> u" and f3: "(wsum, u) \<Rightarrow> t" using WhileE a1 by auto
    from f2 have f4: "u = s(''y'' := s ''y'' + s ''x'', ''x'' := s ''x'' - 1)"
      apply (subst (asm) a2)
      apply (erule SeqE)
      apply (erule AssignE)+
      by simp
    hence f5: "u ''x'' = int n" using Suc by simp
    with Suc f2 f3 have "t ''y'' = u ''y'' + \<Sum> {0..u ''x''}" by simp
    moreover from f4 have "u ''y'' = s ''y'' + int (Suc n)"
      by (simp add: Suc.prems(1))
    ultimately have "t ''y'' = s ''y'' + int (Suc n) + \<Sum> {0..u ''x''}" by simp
    hence "t ''y'' = s ''y'' + s ''x'' + \<Sum> {0..u ''x''}" using Suc by simp
    moreover have "1 + u ''x'' = s ''x''" using f4 by simp
    ultimately show ?case apply clarsimp
      by (smt (verit) Suc.prems(1) f5 int_ops(1) o_apply sum.atLeast0_atMost_Suc sum.atLeast_int_atMost_int_shift)
  qed
  thus ?thesis
    using \<open>(wsum, s) \<Rightarrow> t\<close> nonneg by blast
qed

lemma
assumes a1: "wsum = WHILE Less (N 0) (V ''x'') DO csum"
and a2: "csum = ''y'' ::= Plus (V ''y'') (V ''x'');; ''x'' ::= Plus (V ''x'') (N (-1))"
shows "(''y'' ::= N 0;; wsum, s) \<Rightarrow> t \<Longrightarrow> t ''y'' = (\<Sum>i=0..s ''x''. i)"
apply (erule SeqE)
apply (erule AssignE)
apply simp
using helper a1 a2 by fastforce

end