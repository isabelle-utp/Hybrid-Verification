(*  Title:       Hessian
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

theory Hessian
  imports "HOL-Analysis.Analysis"
    "Sigmoid_Universal_Approximation.Limits_Higher_Order_Derivatives"

begin 


section \<open> Gradient \<close>

text \<open> A definition of the gradient as a vector field (see https://en.wikipedia.org/wiki/Gradient)
and not a single vector as opposed to @{term gderiv}. This choice will be beneficial for users of 
the library. \<close>

(* TODO: this is maybe better known as "gradient field"  *)
definition has_gradient_on :: "(('a::euclidean_space) \<Rightarrow> real) 
  \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" (infix \<open>(has'_gradient'_on)\<close> 50)
  where "(f has_gradient_on g) X \<longleftrightarrow> (\<forall>x\<in>X. (f has_derivative (\<lambda>s. g x \<bullet> s)) (at x within X))"

definition "gradient_of X f = (SOME g. (f has_gradient_on g) X )"

abbreviation "partial_deriv_frac x a e\<^sub>i f df
  \<equiv> (f (a + norm (x - a) *\<^sub>R e\<^sub>i) - f a - df (x - a)) /\<^sub>R norm (x - a)"

abbreviation "partial_deriv_exists F e\<^sub>i f df 
  \<equiv> ((\<lambda>x. partial_deriv_frac x (Lim F (\<lambda>x. x)) e\<^sub>i f df) \<longlongrightarrow> 0) F"

lemma "partial_deriv_exists (at x within X) e\<^sub>i f (\<lambda>s. f' e\<^sub>i) \<longleftrightarrow> K"
  unfolding tendsto_def[where F="at x within X", unfolded eventually_at]
  oops

definition "has_partial_deriv F e\<^sub>i f df \<equiv> (e\<^sub>i \<in> Basis \<and> partial_deriv_exists F e\<^sub>i f df)"

lemma "x \<bullet> One = (sum (\<lambda>e\<^sub>i. x \<bullet> e\<^sub>i) Basis)"
  using inner_sum_right 
  by blast

(* TODO: prove a version of this theorem to corroborate definitions *)
lemma
  assumes has_gradient: "(f has_gradient_on g) X"
    and "e\<^sub>i \<in> Basis"
  shows "\<exists>df. \<forall>x\<in>X. has_partial_deriv (at x within X) e\<^sub>i f (df x)"
proof-
  have obs: "\<forall>x\<in>X. (f has_derivative (\<lambda>s. g x \<bullet> s)) (at x within X)"
    using has_gradient
    by (simp add: has_gradient_on_def)
  {fix x assume "x \<in> X"
    hence "(f has_derivative (\<lambda>s. g x \<bullet> s)) (at x within X)"
      using obs by blast
    thm euclidean_representation_sum_fun[of "g"] inner_sum_left_Basis
    have "has_partial_deriv (at x within X) e\<^sub>i f (\<lambda>s. g s \<bullet> e\<^sub>i)"
      unfolding has_partial_deriv_def
        tendsto_def eventually_at
      sorry
  }
  oops


section \<open> Jacobian \<close>

(* technically, this is really the frechet derivative. To become the true Jacobian: 
(1) 'a \<Rightarrow> 'b should be instantiated to (real ^ 'n) \<Rightarrow> (real ^ 'm)
(2) the second argument of has_derivative should be (\<lambda>s. J x *v s)
Names can be discussed later. *)
definition has_jacobian_on :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) 
  \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" (infix \<open>(has'_jacobian'_on)\<close> 50)
  where "(f has_jacobian_on J) X \<equiv> \<forall>x\<in>X. (f has_derivative (J x)) (at x within X)"

definition "jacobian_of X f = (SOME J. (f has_jacobian_on J) X)"

(* TODO: prove a version of this theorem to corroborate definitions *)
lemma
  assumes has_jacobian: "(f has_jacobian_on J) X"
  shows "has_partial_deriv (at x within X) e\<^sub>i f (\<lambda>x. J x e\<^sub>i)"
proof-
  have obs: "\<forall>x\<in>X. (f has_derivative (\<lambda>s. J x s)) (at x within X)"
    using has_jacobian
    by (simp add: has_jacobian_on_def)
  {fix x assume "x \<in> X"
    hence "(f has_derivative (\<lambda>s. J x s)) (at x within X)"
      using obs by blast
    have "has_partial_deriv (at x within X) e\<^sub>i f (\<lambda>x. J x e\<^sub>i)"
      unfolding has_partial_deriv_def
        tendsto_def eventually_at
      sorry
  }
  oops


section \<open> Hessian \<close>

(* TODO: check if the domain for the jacobian is correct in this definition *)
definition has_hessian_on :: "('a::euclidean_space \<Rightarrow> real) 
  \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool" (infix \<open>(has'_hessian'_on)\<close> 50)
  where "(f has_hessian_on H) X \<equiv> \<exists>g. (f has_gradient_on g) X \<and> (g has_jacobian_on H) X"

definition "hessian_of X f = (SOME H. (f has_hessian_on H) X)"

thm has_gradient_on_def has_jacobian_on_def has_hessian_on_def 
thm bchoice choice
term "GDERIV x y :> k"
thm gderiv_def
term "FDERIV f x :> f' \<longleftrightarrow> (f has_derivative f') (at x)"
term "DERIV f x :> c \<longleftrightarrow> (f has_field_derivative c) (at x)"

section \<open> Nth-derivative \<close>

(* This definition is not ideal. The ones below are better and should imply this one*)
inductive n_differentiable :: "nat \<Rightarrow> 'a filter \<Rightarrow> ('a \<Rightarrow> 'b) 
  \<Rightarrow> ('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) \<Rightarrow> bool"
  where "n_differentiable 0 F f f"
  | "\<lbrakk>n_differentiable m F fm f; (fm has_derivative f') F\<rbrakk> 
    \<Longrightarrow> n_differentiable (Suc m) F f' f"

lemma n_differentiable_zeroD:
  "n_differentiable 0 F g f \<Longrightarrow> f = g"
  by (rule n_differentiable.cases; force)

lemma n_differentiable_witness:
  assumes "n_differentiable (Suc n) F f' f"
  shows "\<exists>fn. n_differentiable n F fn f \<and> (fn has_derivative f') F"
  by (rule n_differentiable.cases[OF assms])
    auto

lemma n_differentiable_SucD:
  assumes "n_differentiable (Suc n) F f' f"
  obtains fn where "n_differentiable n F fn f"
    and "(fn has_derivative f') F"
  using n_differentiable_witness[OF assms]
  by blast


(* Ultimately, for real-valued n-differentiability, this was not necessary.
However, one could explore whether this definition is general enough to the important one below.  *)
inductive n_differentiable_map
  where "dmap 0 = f \<Longrightarrow> n_differentiable_map 0 F dmap f"
  | "\<lbrakk>n_differentiable_map m F dmap f; (dmap m has_derivative dmap (Suc m)) F\<rbrakk> 
    \<Longrightarrow> n_differentiable_map (Suc m) F dmap f"

lemma n_differentiable_map_zeroD:
  "n_differentiable_map 0 F dmap f \<Longrightarrow> dmap 0 = f"
  by (rule n_differentiable_map.cases)
    auto

lemma n_differentiable_map_SucD:
  assumes "n_differentiable_map (Suc n) F dmap f"
  shows "n_differentiable_map n F dmap f"
    "(dmap n has_derivative dmap (Suc n)) F"
  by (rule n_differentiable_map.cases[OF assms]; force)+

lemma n_differentiable_mapD:
  assumes "n_differentiable_map n F dmap f"
  shows "\<forall>m\<le>n. n_differentiable_map m F dmap f"
    and "\<forall>m<n. (dmap m has_derivative dmap (Suc m)) F"
    and "dmap 0 = f"
proof-
  show fst: "\<forall>m\<le>n. n_differentiable_map m F dmap f"
    using assms
    apply (induct rule: n_differentiable_map.induct)
    by (clarsimp intro!: n_differentiable_map.intros)
      (metis le_SucE n_differentiable_map.intros(2))
  show "\<forall>m<n. (dmap m has_derivative dmap (Suc m)) F"
    using assms
    by (induct rule: n_differentiable_map.induct, simp)
      (metis less_Suc_eq)
  show "dmap 0 = f"
    using fst n_differentiable_map_zeroD 
    by blast
qed

lemma n_differentiable_mapI: 
  "\<forall>m<n. (dmap m has_derivative dmap (Suc m)) F
  \<Longrightarrow> dmap 0 = f
  \<Longrightarrow> n_differentiable_map n F dmap f"
  by (induct n)
    (auto intro!: n_differentiable_map.intros)

lemma n_differentiable_map_iff:
  "n_differentiable_map n F dmap f 
  \<longleftrightarrow> (\<forall>m<n. (dmap m has_derivative dmap (Suc m)) F) \<and> dmap 0 = f"
  using n_differentiable_mapD(2,3) n_differentiable_mapI
  by metis

thm DERIV_deriv_iff_real_differentiable[unfolded has_field_derivative_def]
thm DERIV_imp_deriv has_real_derivative_iff
thm has_field_derivative_def has_real_derivative
thm has_derivative_bounded_linear real_bounded_linear
thm deriv_def[no_vars] has_field_derivative_def
  frechet_derivative_def[no_vars]
thm continuous_on_def continuous_def continuous_on_eq_continuous_within

(* key observations for the upcoming definition *)
lemma "deriv f = (\<lambda>x. SOME D. (f has_derivative (\<lambda>y. D * y)) (at x))"
  unfolding deriv_def
  by (simp add: fun_eq_iff has_field_derivative_def)

lemma
  assumes "(deriv^^n) f differentiable at (x::real)"
  shows "((deriv^^n) f has_real_derivative (deriv ^^ (Suc n)) f x) (at x)"
  using DERIV_deriv_iff_real_differentiable[THEN iffD2, OF assms]
  by simp

abbreviation "deriv_frechet F \<equiv> (\<lambda>f. frechet_derivative f F)"

lemma deriv_frechet_differentiableD:
  assumes "((deriv_frechet F)^^n) f differentiable F"
  shows "(((deriv_frechet F)^^n) f has_derivative ((deriv_frechet F)^^(Suc n)) f) F"
  using frechet_derivative_works[THEN iffD1, OF assms]
  by simp

lemma n_differentiable_map_deriv_frechet_iff:
  "n_differentiable_map n F (\<lambda>n. ((deriv_frechet F)^^n) f) f
  \<longleftrightarrow> (\<forall>m<n. ((deriv_frechet F)^^m) f differentiable F)"
  apply (rule iffI)
  unfolding n_differentiable_map_iff 
  by (force simp: differentiable_def)
    (auto dest!: deriv_frechet_differentiableD)

thm frechet_derivative_def frechet_derivative_works
  n_differentiable_map_iff[no_vars] DERIV_deriv_iff_real_differentiable



(* the main definition *)

definition "n_real_differentiable_at n (f::real \<Rightarrow> real) x 
  \<longleftrightarrow> (\<forall>m<n. ((deriv^^m) f) differentiable (at x))"

lemma n_real_differentiable_at_iff: "n_real_differentiable_at n f x
  \<longleftrightarrow> (\<forall>m<n. ((deriv^^m) f has_real_derivative (deriv ^^ (Suc m)) f x) (at x))"
  unfolding n_real_differentiable_at_def DERIV_deriv_iff_real_differentiable[symmetric]
  by simp

lemma Nth_derivative_eq_compow_deriv: 
  "Nth_derivative n f x = (deriv ^^ n) f x"
proof (induct n arbitrary: x)
  fix n x
  assume "\<And>x. Nth_derivative n f x = (deriv ^^ n) f x"
  hence "Nth_derivative n f = (deriv ^^ n) f"
    by (rule ext)
  thus "Nth_derivative (Suc n) f x = (deriv ^^ Suc n) f x"
    by simp
qed simp

lemma n_real_differentiable_atD:
  assumes "n_real_differentiable_at n f x"
  shows "\<forall>m\<le>n. n_real_differentiable_at m f x"
    and "\<forall>m<n. ((deriv^^m) f has_field_derivative (deriv ^^ (Suc m)) f x) (at x)"
    and "\<forall>m<n. (Nth_derivative m f has_field_derivative Nth_derivative (Suc m) f x) (at x)"
proof-
  show "\<forall>m\<le>n. n_real_differentiable_at m f x"
    using assms n_differentiable_mapD(1)
    unfolding n_real_differentiable_at_def
    by fastforce
  show "\<forall>m<n. ((deriv^^m) f has_field_derivative (deriv ^^ (Suc m)) f x) (at x)"
    using assms[unfolded n_real_differentiable_at_iff]
    by blast
  thus "\<forall>m<n. (Nth_derivative m f has_field_derivative Nth_derivative (Suc m) f x) (at x)"
    unfolding Nth_derivative_eq_compow_deriv 
    by simp
qed

(* there are some equalities that could be proven with these lemmas *)
thm DERIV_cmult_Id
thm n_real_differentiable_at_iff[unfolded has_field_derivative_def]
thm n_differentiable_map_deriv_frechet_iff [of n "at x", unfolded frechet_derivative_def]
  n_real_differentiable_at_def[unfolded deriv_def has_field_derivative_def]


(* Taylor's theorem should follow by instantiating here *)
thm MacLaurin.Taylor[of n "\<lambda>n. (deriv ^^ n) f" f]


end