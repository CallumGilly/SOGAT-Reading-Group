theory sogat
imports Main
begin

locale monoid =
  fixes op (infixl "\<cdot>" 75) and u ("\<epsilon>")
  assumes ass: "x \<cdot> (y \<cdot> z) = x \<cdot> y \<cdot> z" and idl [simp]: "\<epsilon> \<cdot> x = x" and idr [simp]: "x \<cdot> \<epsilon> = x"
begin

lemma "\<epsilon> \<cdot> \<epsilon> \<cdot> \<epsilon> = \<epsilon>" by simp
end

(* ex2 *)
interpretation nat_plus_monoid: monoid "(+)" "(0 :: nat)" by unfold_locales simp_all
interpretation nat_times_monoid: monoid "(*)" "(1 :: nat)" by unfold_locales simp_all
interpretation unit_monoid: monoid "(\<lambda> x y. ())" "()" by unfold_locales simp_all
interpretation bool_and_monoid: monoid "(\<and>)" True by unfold_locales simp_all
(* TODO all Boolean monoids *)

(* strings are a monoid - but strings are lists in Isabelle, so lists are a monoid *)
interpretation list_monoid: monoid "(@)" "[]" by unfold_locales simp_all

(* square matrices exist - let's take real n*n matrices for simplicity
consts n :: nat
typedef (overloaded) square = "{M :: real matrix. nrows M = n \<and> ncols M = n}"
proof
  show "(one_matrix n :: real matrix) \<in> {M. nrows M = n \<and> ncols M = n}" by simp
qed
*)
(* TODO show square matrices are a monoid nicely - lifting? *)

(* functions are a monoid under composition *)
interpretation fun_monoid: monoid "(\<circ>)" id by unfold_locales auto

(* sets under union/intersection are a monoid *)
interpretation union_monoid: monoid "(\<union>)" "{}" by unfold_locales auto
interpretation intersection_monoid: monoid "(\<inter>)" "UNIV" by unfold_locales auto
(* /ex2 *)

locale morphism = M1: monoid op1 u1 + M2: monoid op2 u2 for
  op1 (infixl "\<cdot>\<^sub>1" 75) and u1 ("\<epsilon>\<^sub>1") and op2 (infixl "\<cdot>\<^sub>2" 75) and u2 ("\<epsilon>\<^sub>2") +
fixes f
assumes morph_op: "f (x \<cdot>\<^sub>1 y) = (f x) \<cdot>\<^sub>2 (f y)" and morph_u: "f \<epsilon>\<^sub>1 = \<epsilon>\<^sub>2"
begin
end

(* ex3 *)
(* e.g. *)

lemma "morphism (+) (0 :: nat) (\<and>) True (\<lambda> n. n = 0)"
  by unfold_locales simp_all

(* TODO more-phisms *)
(* /ex3 *)

locale dependent_monoid = monoid +
fixes C :: "'m \<Rightarrow> 'a \<Rightarrow> bool" and dop (infixl "\<cdot>\<^sub>D" 75) and du ("\<epsilon>\<^sub>D")
assumes
  op: "\<lbrakk>C x a; C y b\<rbrakk> \<Longrightarrow> C (x \<cdot> y) (a \<cdot>\<^sub>D b)" and
  u:  "C \<epsilon> \<epsilon>\<^sub>D" and
  ass: "a \<cdot>\<^sub>D (b \<cdot>\<^sub>D c) = a \<cdot>\<^sub>D b \<cdot>\<^sub>D c" and
  idl [simp]: "\<epsilon>\<^sub>D \<cdot>\<^sub>D a = a" and
  idr [simp]: "a \<cdot>\<^sub>D \<epsilon>\<^sub>D = a"
begin
end

interpretation vec_dependent_monoid:
  dependent_monoid "(+)" "0 :: nat" "\<lambda> n v. length v = n" "(@)" "[]"
  by unfold_locales simp_all

(* ex4 *)
context monoid
begin

interpretation independent_monoid:
  dependent_monoid "(\<cdot>)" \<epsilon> "\<lambda> _ _. True" "\<lambda> _ _. ()" "()"
  by unfold_locales simp_all
end
