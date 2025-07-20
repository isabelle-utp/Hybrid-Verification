(*  Title:       Hessian
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

theory Hessian
  imports "HOL-Analysis.Analysis"
    "Sigmoid_Universal_Approximation.Limits_Higher_Order_Derivatives"

begin 

(* unbundle derivative_no_notation *)

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


section \<open> Frechet \<close>

definition has_frechet_on :: "('a::real_normed_vector \<Rightarrow> 'b::real_normed_vector) 
  \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool" (infix \<open>(has'_frechet'_on)\<close> 50)
  where "(f has_frechet_on J) X \<equiv> \<forall>x\<in>X. (f has_derivative J) (at x)"

definition "frechet_on X f = (SOME J. (f has_frechet_on J) X)"

thm frechet_derivative_works

lemma "(id has_frechet_on id) UNIV"
  unfolding has_frechet_on_def
  by clarsimp

lemma "(f has_frechet_on Jf1) X
  \<Longrightarrow> (g has_frechet_on Jg1) X
  \<Longrightarrow> ((\<lambda>z. f z + g z) has_frechet_on (\<lambda>y. Jf1 y + Jg1 y)) X"
  unfolding has_frechet_on_def
  by clarify
    (rule has_derivative_add, simp_all)

lemma "(f has_frechet_on Jf1) X
  \<Longrightarrow> \<forall>x\<in>X. (Jf1 has_frechet_on Jf2) X
  \<Longrightarrow> (g has_frechet_on Jg1) X
  \<Longrightarrow> \<forall>x\<in>X. (Jg1 has_frechet_on Jg2) X
  \<Longrightarrow> ((\<lambda>z. f z + g z) has_frechet_on (\<lambda>y. Jf1 y + Jg1 y)) X
    \<and> (\<forall>x\<in>X. ((\<lambda>y. Jf1 y + Jg1 y) has_frechet_on (\<lambda>y. Jf2 y + Jg2 y)) X)"
  unfolding has_frechet_on_def
  by clarsimp

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


section \<open> Nth-derivatives definitions \<close>

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
  "Nth_derivative n f = (deriv ^^ n) f"
  by (induct n)
    simp_all

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

lemma n_real_differentiable_at_iff_le:
  "n_real_differentiable_at n f x \<longleftrightarrow> (\<forall>m\<le>n. n_real_differentiable_at m f x)"
  using n_real_differentiable_atD(1)
  by blast

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

definition "n_real_differentiable_on n f X = (\<forall>x\<in>X. n_real_differentiable_at n f x)"

lemma n_real_differentiable_on_iff_le:
  "n_real_differentiable_on n f X \<longleftrightarrow> (\<forall>m\<le>n. n_real_differentiable_on m f X)"
  unfolding n_real_differentiable_on_def Ball_def
  by (subst n_real_differentiable_at_iff_le)
    blast

lemma n_real_differentiable_on_mono:
  "X \<subseteq> Y \<Longrightarrow> n_real_differentiable_on n f Y \<Longrightarrow> n_real_differentiable_on n f X"
  unfolding n_real_differentiable_on_def
  by blast

primrec k_times_differentiable_at :: "nat \<Rightarrow> (real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool" where
  "k_times_differentiable_at 0 f a  \<longleftrightarrow>  True"                            \<comment> \<open>0 times \<Leftrightarrow> no condition\<close>
| "k_times_differentiable_at (Suc k) f a \<longleftrightarrow>
     (\<exists>\<epsilon>>0.  (\<forall>x. \<bar>x - a\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at k f x))       \<comment> \<open>clause 1\<close>
   \<and> (let g = Nth_derivative k f
      in (g has_derivative (\<lambda>h. Nth_derivative (Suc k) f a * h)) (at a))" \<comment> \<open>clause 2\<close>

lemma k_times_differentiable_atD: 
  "k_times_differentiable_at n f x \<Longrightarrow> \<forall>m\<le>n. k_times_differentiable_at m f x"
  apply (induct n)
   apply simp
  apply clarsimp
  subgoal for n m \<epsilon>
    apply (cases "m \<le> n")
     apply simp
    apply (subgoal_tac "m = Suc n")
    by auto
  done

lemma k_times_differentiable_at_iff_le:
  "k_times_differentiable_at n f x \<longleftrightarrow> (\<forall>m\<le>n. k_times_differentiable_at m f x)"
  using k_times_differentiable_atD
  by blast

lemma n_real_differentiable_on_imp_k_times_diff:
  "\<epsilon> > 0 \<Longrightarrow> n_real_differentiable_on n f (ball x \<epsilon>) \<Longrightarrow> k_times_differentiable_at n f x"
proof (induct n arbitrary: x \<epsilon>)
  case (Suc n)
  hence "\<forall>y\<in>(ball x \<epsilon>). n_real_differentiable_at n f y"
    using n_real_differentiable_on_iff_le[THEN iffD1, OF Suc(3)]
    by (simp add: n_real_differentiable_on_def)
  hence f1: "\<forall>y\<in>(ball x \<epsilon>). k_times_differentiable_at n f y"
    by (metis Suc(1) Elementary_Metric_Spaces.open_ball n_real_differentiable_on_def 
        n_real_differentiable_on_mono open_contains_ball_eq)
  moreover have "(deriv ^^ n) f differentiable (at x)"
    using Suc(3)[unfolded n_real_differentiable_on_def n_real_differentiable_at_def]
    by (simp add: Suc.prems(1))
  ultimately have r1: "(\<exists>\<epsilon>>0. \<forall>y. \<bar>y - x\<bar> < \<epsilon> \<longrightarrow> k_times_differentiable_at n f y)"
    and r2: "((deriv ^^ n) f has_derivative (*) ((deriv ^^ (Suc n)) f x)) (at x)"
    using \<open>0 < \<epsilon>\<close> DERIV_deriv_iff_real_differentiable 
    by (auto simp: ball_def dist_norm has_field_derivative_def)
  show "k_times_differentiable_at (Suc n) f x"
    using r1 r2
    by (auto simp: Nth_derivative_eq_compow_deriv)
qed simp



term Lim
term filterlim
thm Lim_cong_within
thm t2_space_class.Lim_def[of "at x", unfolded tendsto_def eventually_at_topological]




definition "n_diff_on X n jmap oper f 
  \<longleftrightarrow> (\<forall>m<n. \<forall>x\<in>X. (jmap m has_derivative (\<lambda>h. oper (jmap (Suc m) x) h)) (at x within X)) \<and> jmap 0 = f"

lemma n_diff_on_iff_le: 
  "n_diff_on X n jmap oper f  \<longleftrightarrow> (\<forall>m\<le>n. n_diff_on X m jmap oper f)"
  unfolding n_diff_on_def 
  using order_less_le_trans by blast

lemma n_diff_on_iff_Suc: 
  "n_diff_on X (Suc n) jmap oper f \<Longrightarrow> n_diff_on X n jmap oper f"
  unfolding n_diff_on_def
  by auto

lemma "n_diff_on X 1 jmap oper f
  \<longleftrightarrow> (\<forall>x\<in>X. (f has_derivative (\<lambda>h. oper (jmap 1 x) h)) (at x within X)) \<and> jmap 0 = f"
  unfolding n_diff_on_def 
  by (auto simp: has_frechet_on_def)

lemma "\<forall>x\<in>X. (f has_derivative D) (at x within X)
  \<Longrightarrow> \<forall>x\<in>X. f x = g x
  \<Longrightarrow> \<forall>x\<in>X. (g has_derivative D) (at x within X)"
  by (metis has_derivative_transform)

lemma deriv_transfer:
  assumes "open X"
  shows "(f has_derivative (*) f') (at x within X)
 \<Longrightarrow> (g has_derivative (*) g') (at x within X)
 \<Longrightarrow> \<forall>x\<in>X. f x = g x
 \<Longrightarrow> x \<in> X
 \<Longrightarrow> deriv f x = deriv g x"
  using has_derivative_transform[of x X g f] 
    at_within_open_subset[OF _ \<open>open X\<close>, of _ X, simplified]
    DERIV_imp_deriv[unfolded has_field_derivative_def]
  by metis

thm has_derivative_transform at_within_open_subset
lemma n_diff_on_general1: "n_diff_on X n (\<lambda>m. if m = 0 then f else rmap m) (\<lambda>D a. D * a) f
  \<Longrightarrow> open X
  \<Longrightarrow> (\<forall>x\<in>X. n_real_differentiable_at n f x)"
  apply (clarsimp simp: n_diff_on_def n_real_differentiable_at_def)
  subgoal for x m
  proof(induct m arbitrary: x)
    case 0
    then show ?case
      using at_within_open_subset[of _ X X]
      by (force simp: differentiable_def)
  next
    case (Suc m)
    hence IH: "\<And>x. x \<in> X \<Longrightarrow> (deriv ^^ m) f differentiable (at x)"
      "\<forall>m<n. \<forall>x\<in>X. ((if m = 0 then f else rmap m) has_derivative (*) (rmap (Suc m) x)) (at x within X)"
      by auto
    hence fderiv1: "\<And>x. x \<in> X \<Longrightarrow> (f has_derivative (*) (rmap (Suc 0) x)) (at x within X)"
      using Suc.prems(4) by auto
    have fderiv2: "\<And>x. x \<in> X \<Longrightarrow> (f has_derivative (*) (deriv f x)) (at x within X)"
      using IH(2) Suc(5)
      apply (auto elim!: allE[where x=0])
      by (metis DERIV_deriv_iff_real_differentiable Suc.prems(2,3) 
          at_within_open differentiableI has_field_derivative_imp_has_derivative)
    have IH3: "\<forall>m<n. \<forall>x\<in>X. deriv (if m = 0 then f else rmap m) x = (rmap (Suc m) x)"
      using IH(2) DERIV_imp_deriv[unfolded has_field_derivative_def]
        at_within_open_subset[OF _ Suc(3), of _ X, simplified] 
      by fastforce+
    thm deriv_transfer[unfolded field_differentiable_def]
    hence key: "\<forall>m<n. \<forall>x\<in>X. ((deriv ^^ m) f) x = (if m = 0 then f else rmap m) x
        \<and> ((deriv ^^ m) f has_derivative (*) ((deriv ^^ (Suc m)) f x)) (at x within X)"
      apply clarsimp
      apply (rule conjI; clarsimp)
      using fderiv2 apply blast
      subgoal for m' x'
        apply (induct m' arbitrary: x', simp)
        apply (rule conjI, clarsimp)
        subgoal for m' x'
          apply (cases "m' = 0", force)
          apply simp
          apply (subst deriv_transfer[OF Suc(3), of "(deriv ^^ m') f" _ x' "rmap m'"]; clarsimp?)
          apply force
          using IH(2)[rule_format, of m' x'] apply force
          by (erule_tac x=m' in allE, simp)
        subgoal for m' x'
          apply (cases "m' = 0"; clarsimp)
          subgoal
            using IH(2)
            apply (clarsimp elim!: allE[where x=1])
            apply (subgoal_tac "\<forall>x \<in> X. rmap (Suc 0) x = deriv f x")
            using has_derivative_transform[of x' X "deriv f" "rmap (Suc 0)"]
            apply (metis Suc.prems(2) at_within_open deriv_eq)
            using has_derivative_unique[of f "(*) (rmap (Suc 0) _)" _ "(*) (deriv f _)"] fderiv1 fderiv2
              at_within_open_subset[OF _ \<open>open X\<close>, of _ X, simplified]
            by (metis deriv_eq)
          subgoal
            using IH(2)
            apply (clarsimp elim!: allE[where x="Suc m'"])
            apply (subgoal_tac "\<forall>x \<in> X. rmap (Suc m') x = (deriv^^(Suc m')) f x")
             apply (rule has_derivative_transform[of x' X "(deriv^^(Suc m')) f" "rmap (Suc m')", simplified]; simp?)
             apply (smt (verit, best) Suc.prems(2) at_within_open deriv_eq has_derivative_transform)
            apply clarsimp
            apply (rename_tac z)
            apply (subst IH3[rule_format, of m' _, symmetric]; simp)
            apply (rule_tac f'="rmap (Suc m') z" in deriv_transfer[OF \<open>open X\<close>]; simp?)
            using IH(2)[rule_format, of m' _] apply simp
            by force
        done
      done
    done
    have "\<forall>x\<in>X. (rmap (Suc m) has_derivative (*) (rmap (Suc (Suc m)) x)) (at x within X)"
      using Suc(5) IH(2)
      by auto
    hence "\<forall>x\<in>X. ((deriv ^^ (Suc m)) f has_derivative (*) (rmap (Suc (Suc m)) x)) (at x within X)"
      using has_derivative_transform[of _ _ "(deriv ^^ Suc m) f" "rmap (Suc m)"]
        key[rule_format, OF Suc(5), simplified, THEN conjunct1, symmetric] 
      by force
    thus "(deriv ^^ Suc m) f differentiable at x"
      using Suc(4) at_within_open_subset[OF _ Suc(3), of _ X, simplified] 
      by (auto simp: differentiable_def)
  qed
  done

lemma n_diff_on_general2: "n_diff_on X n (\<lambda>m. if m = 0 then f else rmap m) (\<lambda>D a. D * a) f
  \<Longrightarrow> open X
  \<Longrightarrow> n_real_differentiable_on n f X"
  unfolding n_real_differentiable_on_def
  using n_diff_on_general1 by simp

lemma n_diff_on_general3: "n_diff_on (ball x \<epsilon>) n (\<lambda>m. if m = 0 then f else rmap m) (\<lambda>D a. D * a) f
  \<Longrightarrow> 0 < \<epsilon>
  \<Longrightarrow> k_times_differentiable_at n f x"
  by (rule n_real_differentiable_on_imp_k_times_diff, force)
    (rule n_diff_on_general2; force)

thm deriv_transfer has_derivative_transform
lemma deriv_n_transfer_on_open:
  fixes f g :: "real \<Rightarrow> real"
  assumes "open X" "x \<in> X"
    and eq_onX: "\<And>x. x \<in> X \<Longrightarrow> f x = g x"
    and f_has:   "\<forall>m\<le>k. \<forall>x\<in>X. ((deriv^^ m) f has_derivative (\<lambda>h. (deriv^^(Suc m)) f x * h)) (at x within X)"
  shows "((deriv^^ k) g  has_derivative (\<lambda>h. (deriv^^(Suc k)) f x * h)) (at x within X)"
  using \<open>x \<in> X\<close> f_has
proof(induct k arbitrary: x rule: nat_less_induct)
  case (1 n)
  have "\<And>x. x \<in> X \<Longrightarrow> (deriv ^^ n) g x = (deriv ^^ n) f x"
    apply (cases "n = 0"; simp)
    using eq_onX apply force
    apply (subgoal_tac "\<exists>m. n = Suc m", clarsimp)
     apply (rule deriv_eq)
     apply (subst at_within_open[OF _ \<open>open X\<close>, of _, symmetric], simp)
     apply (rule 1(1)[rule_format, simplified]; force?)
    using 1(3) apply force
    by (simp add: not0_implies_Suc)
  moreover have "((deriv ^^ n) f has_derivative (*) (deriv ((deriv ^^ n) f) x)) (at x within X)"
    using 1(3) 1(2)
    by simp
  ultimately have "((deriv ^^ n) g has_derivative (*) (deriv ((deriv ^^ n) f) x)) (at x within X)"
    by (rule has_derivative_transform[OF \<open>x \<in> X\<close>, of _ "(deriv ^^ n) f"])
      simp
  thus "((deriv ^^ n) g has_derivative (*) ((deriv ^^ Suc n) f x)) (at x within X)"
    by simp
qed

lemma Nth_derivative_transfer_on_ball:
  fixes f g :: "real \<Rightarrow> real"
  assumes \<epsilon>_pos: "0 < \<epsilon>"
      and eq_ball: "\<forall>y. y \<in> ball x \<epsilon> \<longrightarrow> f y = g y"
      and f_has:   "\<forall>m\<le>k. \<forall>y\<in>ball x \<epsilon>. (Nth_derivative m f
                      has_derivative (\<lambda>h. Nth_derivative (Suc m) f x * h)) (at y)"
  shows   "(Nth_derivative k g
              has_derivative (\<lambda>h. Nth_derivative (Suc k) f x * h)) (at x)"
  using f_has
  unfolding Nth_derivative_eq_compow_deriv
  apply (subst at_within_open[symmetric, of x "ball x \<epsilon>"]; simp add: \<epsilon>_pos)
  apply (rule deriv_n_transfer_on_open[simplified]; (simp add: \<epsilon>_pos)?)
  using eq_ball apply force
  using at_within_open[of _ "ball x \<epsilon>", simplified]
  by (metis deriv_eq has_derivative_at_withinI)

end