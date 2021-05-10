theory HS_Lens
  imports Derivative_extra Optics.Optics
begin

locale cont_lens = vwb_lens +
  assumes bounded_linear_get: "bounded_linear get"
  and bounded_linear_put: "bounded_linear (\<lambda> (s, v). put s v)"
begin

lemma has_derivative_put: "((\<lambda> (s, v). put s v) has_derivative (\<lambda> (s, v). put s v)) (at t within X)"
  using bounded_linear_imp_has_derivative bounded_linear_put by blast
  
lemma has_derivative_put':
  assumes "bounded_linear f" "(g has_derivative g') (at t within X)"
  shows "((\<lambda>s. put (f s) (g s)) has_derivative (\<lambda>s. put (f s) (g' s))) (at t within X)"
proof -
  have 1: "((\<lambda>s. (f s, g s)) has_derivative (\<lambda>s. (f s, g' s))) (at t within X)"
    by (simp add: assms bounded_linear_imp_has_derivative has_derivative_Pair)
    
  from has_derivative_compose[OF 1 has_derivative_put]
  show ?thesis
    by (simp add: prod.case_eq_if)

qed

end

lemma cont_lens_vwb [simp]: "cont_lens x \<Longrightarrow> vwb_lens x"
  by (simp add: cont_lens_def)
  
lemma cont_lens_bounded_linear [simp]: "cont_lens x \<Longrightarrow> bounded_linear get\<^bsub>x\<^esub>"
  by (simp add: cont_lens.bounded_linear_get)

lemma cont_lens_intro:
  assumes 
    "vwb_lens x" "bounded_linear get\<^bsub>x\<^esub>" "bounded_linear (\<lambda> (s, v). put\<^bsub>x\<^esub> s v)"
  shows "cont_lens x"
proof -
  interpret vwb_lens x by (simp add: assms)
  show ?thesis by (intro_locales, simp add: cont_lens_axioms_def assms)
qed

lemma cont_lens_one [simp]: "cont_lens id_lens"
proof -
  have b: "bounded_linear (\<lambda> (x, y). y)"
    using bounded_linear_snd by (metis cond_case_prod_eta snd_conv) 
  show ?thesis
    by (rule_tac cont_lens_intro, simp_all, simp_all add: lens_defs id_def snd_def b)
qed  

lemma cont_lens_fst [simp]: "cont_lens fst\<^sub>L"
  by (rule cont_lens_intro, simp add: fst_vwb_lens, simp_all add: lens_defs split_beta' bounded_linear_intros)

lemma cont_lens_snd [simp]: "cont_lens snd\<^sub>L"
  by (rule cont_lens_intro, simp add: snd_vwb_lens, simp_all add: lens_defs split_beta' bounded_linear_intros)

lemma bounded_linear_lens_comp_put:
  assumes "vwb_lens x" "bounded_linear (\<lambda> (s, v). put\<^bsub>x\<^esub> s v)"
    "vwb_lens y" "bounded_linear (\<lambda> (s, v). put\<^bsub>y\<^esub> s v)"
    "bounded_linear get\<^bsub>y\<^esub>"
  shows "bounded_linear (\<lambda>(s, v). put\<^bsub>y\<^esub> s (put\<^bsub>x\<^esub> (get\<^bsub>y\<^esub> s) v))"
proof -
  from bounded_linear_compose[OF assms(2) bounded_linear_Pair[OF bounded_linear_compose[OF assms(5) bounded_linear_fst] bounded_linear_snd]]
  have 1: "bounded_linear (\<lambda> (s, v). put\<^bsub>x\<^esub> (get\<^bsub>y\<^esub> s) v)"
    by (simp add: split_beta')

  from bounded_linear_compose[OF assms(4) bounded_linear_Pair[OF bounded_linear_fst 1]]
  show ?thesis  
    by (simp add: split_beta')
qed

lemma cont_lens_comp [simp]:
  fixes x :: "'a::real_normed_vector \<Longrightarrow> 'b::real_normed_vector" 
    and y :: "'b \<Longrightarrow> 'c::real_normed_vector"
  assumes "cont_lens x" "cont_lens y"
  shows "cont_lens (x ;\<^sub>L y)"
  using assms 
  apply (rule_tac cont_lens_intro, simp_all add: comp_vwb_lens)
   apply (simp_all add: bounded_linear_lens_comp_put cont_lens.bounded_linear_put lens_comp_def)
  apply (simp add: bounded_linear_compose comp_def)
  done

end
