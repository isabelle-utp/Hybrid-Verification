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
thm DERIV_deriv_iff_real_differentiable[unfolded has_field_derivative_def]
thm DERIV_imp_deriv has_real_derivative_iff
thm has_field_derivative_def has_real_derivative
thm has_derivative_bounded_linear real_bounded_linear
thm deriv_def[no_vars] has_field_derivative_def
  frechet_derivative_def[no_vars]
thm continuous_on_def continuous_def continuous_on_eq_continuous_within


section \<open> Nth-derivative \<close>

inductive n_differentiable_map_at
  where "dmap 0 = f \<Longrightarrow> n_differentiable_map_at x 0 oper dmap f"
  | "n_differentiable_map_at x m oper dmap f
    \<Longrightarrow> (dmap m has_derivative (\<lambda>y. oper (dmap (Suc m)) y)) (at x) 
    \<Longrightarrow> n_differentiable_map_at x (Suc m) oper dmap f"

lemma n_differentiable_map_at_zeroD:
  "n_differentiable_map_at x 0 oper dmap f \<Longrightarrow> dmap 0 = f"
  by (rule n_differentiable_map_at.cases)
    auto

lemma n_differentiable_map_at_SucD:
  assumes "n_differentiable_map_at x (Suc n) oper dmap f"
  shows "n_differentiable_map_at x n oper dmap f"
    "(dmap n has_derivative (\<lambda>y. oper (dmap (Suc n)) y)) (at x)"
  by (rule n_differentiable_map_at.cases[OF assms]; force)+

lemma n_differentiable_map_atD:
  assumes "n_differentiable_map_at x n oper dmap f"
  shows "\<forall>m\<le>n. n_differentiable_map_at x m oper dmap f"
    and "\<forall>m<n. (dmap m has_derivative (\<lambda>y. oper (dmap (Suc m)) y)) (at x)"
    and "dmap 0 = f"
proof-
  show fst: "\<forall>m\<le>n. n_differentiable_map_at x m oper dmap f"
    using assms
    apply (induct rule: n_differentiable_map_at.induct)
    by (clarsimp intro!: n_differentiable_map_at.intros)
      (metis le_SucE n_differentiable_map_at.intros(2))
  show "\<forall>m<n. (dmap m has_derivative (\<lambda>y. oper (dmap (Suc m)) y)) (at x)"
    using assms
    by (induct rule: n_differentiable_map_at.induct, simp)
      (metis less_Suc_eq)
  show "dmap 0 = f"
    using fst n_differentiable_map_at_zeroD 
    by blast
qed

lemma n_differentiable_map_atI: 
  "\<forall>m<n. (dmap m has_derivative (\<lambda>y. oper (dmap (Suc m)) y)) (at x)
  \<Longrightarrow> dmap 0 = f
  \<Longrightarrow> n_differentiable_map_at x n oper dmap f"
  by (induct n arbitrary: x)
    (auto intro!: n_differentiable_map_at.intros)

lemma n_differentiable_map_at_iff:
  "n_differentiable_map_at x n oper dmap f 
  \<longleftrightarrow> (\<forall>m<n. (dmap m has_derivative (\<lambda>y. oper (dmap (Suc m)) y)) (at x)) \<and> dmap 0 = f"
  using n_differentiable_map_atD(2,3) n_differentiable_map_atI
  by metis


(* observations for the upcoming definition *)

(* deriv is already the derivative operator *)
lemma "deriv f = (\<lambda>x. SOME D. (f has_derivative (\<lambda>y. D * y)) (at x))"
  unfolding deriv_def
  by (simp add: fun_eq_iff has_field_derivative_def)

lemma deriv_differentiable_atD:
  assumes "(deriv^^n) f differentiable at (x::real)"
  shows "((deriv^^n) f has_real_derivative (deriv ^^ (Suc n)) f x) (at x)"
  using DERIV_deriv_iff_real_differentiable[THEN iffD2, OF assms]
  by simp

(* frechet_derivative is already the derivative operator *)
abbreviation "deriv_frechet F \<equiv> (\<lambda>f. frechet_derivative f F)"

lemma deriv_frechet_differentiableD:
  assumes "((deriv_frechet F)^^n) f differentiable F"
  shows "(((deriv_frechet F)^^n) f has_derivative ((deriv_frechet F)^^(Suc n)) f) F"
  using frechet_derivative_works[THEN iffD1, OF assms]
  by simp

lemma n_differentiable_map_at_deriv_frechet_iff:
  "n_differentiable_map_at x n (\<lambda>\<D> y. \<D> y) (\<lambda>n. ((deriv_frechet (at x))^^n) f) f
  \<longleftrightarrow> (\<forall>m<n. ((deriv_frechet (at x))^^m) f differentiable (at x))"
  apply (rule iffI)
  unfolding n_differentiable_map_at_iff 
  by (force simp: differentiable_def)
    (auto dest!: deriv_frechet_differentiableD)


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
    using assms n_differentiable_map_atD(1)
    unfolding n_real_differentiable_at_def
    by fastforce
  show "\<forall>m<n. ((deriv^^m) f has_field_derivative (deriv ^^ (Suc m)) f x) (at x)"
    using assms[unfolded n_real_differentiable_at_iff]
    by blast
  thus "\<forall>m<n. (Nth_derivative m f has_field_derivative Nth_derivative (Suc m) f x) (at x)"
    unfolding Nth_derivative_eq_compow_deriv 
    by simp
qed

lemma n_differentiable_map_at_iff_n_real_differentiable_at:
  "n_differentiable_map_at x n (\<lambda>\<D> y. \<D> x * y) (\<lambda>m. (deriv^^m) f) f
  \<longleftrightarrow> n_real_differentiable_at n f x"
  unfolding n_real_differentiable_at_iff n_differentiable_map_at_iff
      has_field_derivative_def by simp

lemma frechet_derivative_eq: 
  "(f has_derivative f') (at x) \<Longrightarrow> frechet_derivative f (at x) = f'"
  unfolding frechet_derivative_def
  using has_derivative_unique by blast

lemma deriv_eq: "(f has_derivative (\<lambda>y. D * y)) (at x) \<Longrightarrow> deriv f x = D"
  unfolding frechet_derivative_def deriv_def 
  using DERIV_unique has_field_derivative_def by blast

lemma frechet_derivative_eq_deriv:
  fixes f :: "'a::real_normed_field \<Rightarrow> 'a"
  assumes "(f has_derivative (\<lambda>y. D * y)) (at x)"
  shows "frechet_derivative f (at x) 1 = D"
    and "frechet_derivative f (at x) 1 = deriv f x"
  using frechet_derivative_eq[OF assms] deriv_eq[OF assms]
  by auto

(* OBS: despite @{thm "n_differentiable_map_at_iff_n_real_differentiable_at"},
we cannot prove that any map witnessing n_differentiable_map_at will
also witness n_real_differentiable_at (see below). The only map that works is
(\<lambda>m. (deriv^^m) f). In that sense, @{term "n_differentiable_map_at"} is more
general.
*)
lemma "n_differentiable_map_at x n (\<lambda>\<D> y. \<D> x * y) (\<lambda>m. if m = 0 then f else rmap m) f
  \<longleftrightarrow> n_real_differentiable_at n f x" (is "n_differentiable_map_at x n ?oper ?dmap f \<longleftrightarrow> _")
proof
  assume hyp: "n_differentiable_map_at x n ?oper ?dmap f"
  hence key: "\<forall>m<n. (?dmap m has_derivative (*) (rmap (Suc m) x)) (at x)"
    using n_differentiable_map_atD(2)[OF hyp] 
    by auto
  have "n = 0 \<Longrightarrow> n_real_differentiable_at n f x"
    unfolding n_real_differentiable_at_def by simp
  have "0 < n \<Longrightarrow> m < n \<Longrightarrow> ((deriv^^m) f has_derivative (*) (rmap (Suc m) x)) (at x)" for m::nat
  proof(induct m)
    case 0
    thus ?case
      using key
      by auto
  next
    thm deriv_differentiable_atD
    case (Suc m)
    hence IH: "((deriv^^m) f has_derivative (\<lambda>y. rmap (Suc m) x * y)) (at x)"
      using Suc_lessD by auto
    (* here we need differentiability in the neighbourhood, not just x *)
    have eq1: "(deriv ^^ Suc m) f x = rmap (Suc m) x"
      using DERIV_imp_deriv[unfolded has_field_derivative_def, OF IH(1)]
      by simp
    have key_sucm: "(rmap (Suc m) has_derivative (*) (rmap (Suc (Suc m)) x)) (at x)"
      using key Suc
      by auto
    thm DERIV_imp_deriv[unfolded has_field_derivative_def, OF key_sucm, unfolded ] 
      eq1[symmetric, simplified]
    then show "((deriv ^^ Suc m) f has_derivative (*) (rmap (Suc (Suc m)) x)) (at x)"
    oops

lemma Taylor_theorem:
  "\<forall>t. a \<le> t \<longrightarrow> t \<le> b \<longrightarrow> n_real_differentiable_at n f t
 \<Longrightarrow> \<lbrakk>0 < n; a \<le> c; c \<le> b; a \<le> x; x \<le> b; x \<noteq> c\<rbrakk>
 \<Longrightarrow> \<exists>t. (if x < c then x < t \<and> t < c else c < t \<and> t < x) \<and>
    f x = (\<Sum>m<n. ((deriv^^m) f) c / fact m * (x - c) ^ m) + ((deriv^^n) f) t / fact n * (x - c) ^ n"
  using n_real_differentiable_atD(2)[of n f]
  by - (rule MacLaurin.Taylor, auto) 

lemma "n_real_differentiable_at n f x \<Longrightarrow> n_real_differentiable_at n g x 
  \<Longrightarrow> m < n
  \<Longrightarrow> ((deriv^^m) (\<lambda>w. f w + g w) x = (deriv ^^ m) f x + (deriv ^^ m) g x)"
  apply (induct m arbitrary: n)
   apply simp
  apply simp
    (* again we require differentiability in a neighbourhood of x *)
  unfolding n_real_differentiable_at_iff
  using deriv_add
  using DERIV_deriv_iff_field_differentiable DERIV_imp_deriv 
  oops

thm at_within_open_subset


end