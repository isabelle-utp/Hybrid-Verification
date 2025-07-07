(*  Title:       Hessian
    Maintainer:  Jonathan Julián Huerta y Munive <jonjulian23@gmail.com>
*)

theory Hessian
  imports "HOL-Analysis.Analysis"

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

end