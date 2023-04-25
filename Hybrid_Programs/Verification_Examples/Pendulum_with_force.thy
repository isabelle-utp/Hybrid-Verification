theory Pendulum_with_force
  imports "Hybrid-Verification.Proof_Automation"
begin

dataspace sys = 
  constants g :: real L :: real k :: real
  assumes L_gr_0: "L \<noteq> 0" and K_gr_0: "k > 0" and g_gr_0: "g > 0"
  variables w :: real \<theta> :: real push :: real
context sys
begin

declare L_gr_0 [simp]

abbreviation "program \<equiv> LOOP ((push ::= ? ; IF (1/2 * (w - push)\<^sup>2 < g / L * cos(\<theta>)) THEN w ::= w - push ELSE skip);
                              {\<theta>` = w, w` = -g/L * sin(\<theta>) - k * w}) INV (g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)"

lemma "\<^bold>{(g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)\<^bold>} {\<theta>` = w, w` = -g/L * sin(\<theta>) - k * w} \<^bold>{(g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)\<^bold>}"
  apply dInduct_auto
  using K_gr_0 by auto

lemma "\<^bold>{(g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)\<^bold>} (push ::= ? ; IF (1/2 * (w - push)\<^sup>2 < g / L * cos(\<theta>)) THEN w ::= w - push ELSE skip) \<^bold>{(g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L)\<^bold>}"
  apply wlp_simp
  apply (simp_all add: usubst_eval)
  apply (expr_auto)
  sorry

lemma "`g / L * (1 - cos(\<theta>)) + (1/2 * w\<^sup>2) < g / L \<longrightarrow> pi / 2 < \<theta> \<and> \<theta> < pi / 2`"
  apply (expr_auto)
  sorry


end



end