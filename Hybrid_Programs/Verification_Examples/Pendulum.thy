theory Pendulum
  imports "Hybrid-Verification.Hybrid_Verification"

begin



dataspace pendulum =
  constants r :: real
  variables 
    x :: real 
    y :: real

context pendulum
begin

\<comment> \<open>Verified with annotated dynamics \<close>

abbreviation "pend_flow \<tau> \<equiv> [
  x \<leadsto> x * cos \<tau> + y * sin \<tau>, 
  y \<leadsto> - x * sin \<tau> + y * cos \<tau>]"

lemma pendulum_dyn: 
  "H{\<guillemotleft>r\<guillemotright>\<^sup>2 = ($x)\<^sup>2 + ($y)\<^sup>2} (EVOL pend_flow G U) {\<guillemotleft>r\<guillemotright>\<^sup>2 = ($x)\<^sup>2 + ($y)\<^sup>2}"
  by (simp add: fbox_g_evol) expr_auto

\<comment> \<open>Verified with Framed derivatives \<close>

lemma pendulum_lie: "H{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2} {x` = y, y` = - x} {\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2}"
  by dInduct

\<comment> \<open>Verified with differential invariants as cartesian product \<close>

lemma pendulum_inv: "H{\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2} {(x, y)` = (y, -x)} {\<guillemotleft>r\<guillemotright>\<^sup>2 = x\<^sup>2 + y\<^sup>2}"
  apply(simp add: hoare_diff_inv_on')
  apply(rule diff_inv_on_eqI)
  apply (simp add: var_pair_def)
  apply clarsimp+
  apply expr_simp
  apply (auto intro!: vderiv_intros )
  done

end


end