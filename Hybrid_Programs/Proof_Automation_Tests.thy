
theory Proof_Automation_Tests
  imports Proof_Automation

begin


dataspace basic_tests = 
  variables 
    x :: real
    y :: real
    z :: real

context basic_tests
begin

lemma "H{True} skip {True}"
  by wlp_simp

lemma "H{True} abort {P \<and> \<not> P}"
  by wlp_simp

lemma "H{True} \<questiondown>x > 0? {x > 0}"
  by wlp_simp

lemma "H{True} x := 1 {x = 1}"
  by wlp_simp

lemma "H{True} x := ? {x \<in> UNIV}"
  by wlp_simp

lemma "H{True} x := 1 \<sqinter> x := 2 {x > 0}"
  by wlp_simp

end


dataspace wlp_testing =
  constants 
    A::real 
    B::real 
    S::real 
    V::real 
    \<epsilon>::real
  variables 
    x::real 
    v::real 
    a::real 
    c::real 
    d::real

declare [[literal_variables=true]]
no_notation (ASCII) disj (infixr "|" 30)

context wlp_testing
begin

lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2 * B) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) + (A/B + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= A) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B; d ::= ?)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)}
    )
   INV (v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S \<and> \<epsilon> > 0)
  ] (x \<le> S)"
  apply (wlp_solve "(\<lambda>t. [c \<leadsto> t + c, x \<leadsto> a * t\<^sup>2 / 2 + v * t + x, v \<leadsto> a * t + v])")
  by expr_auto 
    (smt (verit) divide_nonneg_nonneg zero_le_power)

lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2 * B) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) + (A/B + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= A) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B; d ::= ?)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)}
    )
   INV (v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S \<and> \<epsilon> > 0)
  ] (x \<le> S)"
  apply (wlp_expr_solve "(\<lambda>t. [c \<leadsto> t + c, x \<leadsto> a * t\<^sup>2 / 2 + v * t + x, v \<leadsto> a * t + v])")
  apply (smt (verit) divide_nonneg_nonneg zero_le_power)
  done

lemma local_flow_test: "local_flow_on [c \<leadsto> 1, v \<leadsto> a, x \<leadsto> v] (x +\<^sub>L v +\<^sub>L c) UNIV UNIV
  (\<lambda>t. [c \<leadsto> t + c, x \<leadsto> a * t\<^sup>2 / 2 + v * t + x, v \<leadsto> a * t + v])"
  by local_flow_on_auto

lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2 * B) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) + (A/B + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= A) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B; d ::= ?)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)}
    )
   INV (v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S \<and> \<epsilon> > 0)
  ] (x \<le> S)"
  apply (wlp_simp local_flow: local_flow_test)
  by expr_auto 
    (smt (verit) divide_nonneg_nonneg zero_le_power)

lemma "(v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2 * B) \<le> S \<and> \<epsilon> > 0)\<^sub>e \<le>
  |LOOP 
    ((\<questiondown>x + v\<^sup>2/(2*B) + (A/B + 1)*(A/2*\<epsilon>\<^sup>2 + \<epsilon> * v) \<le> S?; a ::= A) 
      \<sqinter> (\<questiondown>v=0?; a ::= 0) 
      \<sqinter> (a ::= - B; d ::= ?)
    );(
      (c ::= 0); 
      {x` = v, v` = a, c` = 1 | (v \<ge> 0 \<and> x + v\<^sup>2/(2*B) \<le> S)}
    )
   INV (v \<ge> 0 \<and> A > 0 \<and> B > 0 \<and> x + v\<^sup>2/(2*B) \<le> S \<and> \<epsilon> > 0)
  ] (x \<le> S)"
  apply (wlp_full local_flow: local_flow_test)
  apply (smt (verit) divide_nonneg_nonneg zero_le_power)
  done

end
