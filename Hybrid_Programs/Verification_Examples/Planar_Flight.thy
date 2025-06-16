theory Planar_Flight
  imports "Hybrid-Verification.Hybrid_Verification"
begin

dataspace planar_flight =
  constants
    v\<^sub>o :: real (* own_velocity *)
    v\<^sub>i :: real (* intruder velocity *)
  assumes
    v\<^sub>o_pos: "v\<^sub>o > 0" and
    v\<^sub>i_pos: "v\<^sub>i > 0"
  variables (* Coordinates in reference frame of own ship *)
    x :: real (* Intruder x *)
    y :: real (* Intruder y *)
    \<theta> :: real (* Intruder angle *)
    \<omega> :: real (* Angular velocity *)

context planar_flight
begin

(*

Invariants obtained from:

Khalil Ghorbal, Jean-Baptiste Jeannin, Erik Zawadzki, André Platzer, Geoffrey J. Gordon,
and Peter Capell. Hybrid Theorem Proving of Aerospace Systems: Applications and Challenges. 
J. Aerospace Inf. Sys., 2014, 11 (10), pp.702--713. https://doi.org/10.2514/1.I010178

Which used the methods described in:

Ghorbal, K., Platzer, A. (2014). Characterizing Algebraic Invariants by Differential 
Radical Invariants. In: Ábrahám, E., Havelund, K. (eds) Tools and Algorithms for the 
Construction and Analysis of Systems. TACAS 2014. Lecture Notes in Computer Science, 
vol 8413. Springer, Berlin, Heidelberg. https://doi.org/10.1007/978-3-642-54862-8_19

*)

expression I is "v\<^sub>i * sin \<theta> * x - (v\<^sub>i * cos \<theta> - v\<^sub>o) * y > v\<^sub>o + v\<^sub>i"

expression J is "v\<^sub>i * \<omega> * sin \<theta> * x - v\<^sub>i * \<omega> * cos \<theta> * y 
                  + v\<^sub>o * v\<^sub>i * cos \<theta> 
                  > v\<^sub>o * v\<^sub>i + v\<^sub>i * \<omega>"

definition "ctrl = (\<omega> ::= 0; \<questiondown>I?) \<sqinter> (\<omega> ::= 1; \<questiondown>J?)"

definition "plant = {x` = v\<^sub>i * cos \<theta> - v\<^sub>o + \<omega> * y,
                     y` = v\<^sub>i * sin \<theta> - \<omega> * x,
                     \<theta>` = -\<omega>}"

definition "flight = (ctrl; plant)\<^sup>*"

lemma flight_safe: "H{x\<^sup>2 + y\<^sup>2 > 0} flight {x\<^sup>2 + y\<^sup>2 > 0}"
  unfolding flight_def ctrl_def plant_def
  apply kstar
  apply (sequence "(\<omega> = 0 \<and> I) \<or> (\<omega> = 1 \<and> J)")
   apply wlp_full
  apply split_invariant
   apply (invariant "\<omega> = 0 \<and> I")
  apply (dInduct_mega)
  apply expr_auto
  apply expr_auto
  using sum_power2_gt_zero_iff v\<^sub>i_pos v\<^sub>o_pos apply fastforce
  apply (invariant "\<omega>=1 \<and> J")
    apply dInduct_mega
   apply expr_auto
  apply expr_auto
  apply (smt (verit) Groups.mult_ac(2) abs_cos_le_one mult_eq_0_iff mult_left_le_one_le v\<^sub>i_pos v\<^sub>o_pos zero_compare_simps(6)
      zero_le_power2 zero_less_power2)
  done

end


declare [[literal_variables=false]]

lemma diffInvariant:
  assumes "H{I} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 {I}" "`P \<longrightarrow> I`"
          "H{P} g_orbital_on a f (G \<and> I)\<^sub>e (U)\<^sub>e S t\<^sub>0 {Q}"
  shows "H{P} g_orbital_on a f (G)\<^sub>e (U)\<^sub>e S t\<^sub>0 {Q}"
  apply (rule diff_cut_on_rule[where C=I])
  using assms weaken apply fastforce
  using assms by simp

method dInv for I :: "'st \<Rightarrow> bool" uses facts =
  (rule diffInvariant[where I="I"],
   (dInduct_mega facts: facts)[1],
   (expr_auto)[1])


context planar_flight
begin

lemma flight_safe2: "H{x\<^sup>2 + y\<^sup>2 > 0} flight {x\<^sup>2 + y\<^sup>2 > 0}"
proof -
  have ctrl_post: "H{x\<^sup>2 + y\<^sup>2 > 0} ctrl {(\<omega> = 0 \<and> @I) \<or> (\<omega> = 1 \<and> @J)}"
    unfolding ctrl_def by wlp_full

  have plant_safe_I: "H{\<omega> = 0 \<and> @I} plant {x\<^sup>2 + y\<^sup>2 > 0}"
    unfolding plant_def apply (dInv "($\<omega> = 0 \<and> @I)\<^sup>e", dWeaken)
    using v\<^sub>o_pos v\<^sub>i_pos sum_squares_gt_zero_iff by fastforce

  have plant_safe_J: "H{\<omega> = 1 \<and> @J} plant {x\<^sup>2 + y\<^sup>2 > 0}"
    unfolding plant_def apply (dInv "(\<omega>=1 \<and> @J)\<^sup>e", dWeaken)
    by (metis add.right_neutral cos_le_one distrib_left less_add_same_cancel2 
        linorder_not_le linordered_comm_semiring_strict_class.comm_mult_strict_left_mono 
        mult.right_neutral mult_zero_left not_less_iff_gr_or_eq pos_add_strict 
        sum_squares_gt_zero_iff v\<^sub>i_pos v\<^sub>o_pos)

    show ?thesis
    unfolding flight_def apply (intro hoare_kstar_inv hoare_kcomp[OF ctrl_post])
    by (rule hoare_disj_split[OF plant_safe_I plant_safe_J])
qed

end

end