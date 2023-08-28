theory UnknownParticipation
  imports Main "HOL-Library.Multiset"
begin

section "Lemmas about majorities"

definition majority where \<comment> \<open>@{term A} is a strict majority among @{term B}\<close>
  "majority A B \<equiv> A \<subseteq> B \<and> 2*(card A) > card B"

text \<open>To make proofs simpler we assume that the set of processors is finite.
We could rewrite the proofs using explicit finiteness assumptions when needed (e.g. the set of participants is always finite)\<close>

lemma majorities_intersect:
  fixes A B C :: "('p::finite) set"
  assumes "C \<noteq> {}" and "majority A C" and "majority B C"
  shows "A \<inter> B \<noteq> {}"
proof (rule ccontr; simp) \<comment> \<open>proof by contradiction\<close>
  assume "A \<inter> B = {}"
  hence "card C \<ge> card A + card B"
    by (metis Un_least assms(2) assms(3) card_Un_disjoint card_mono finite_code majority_def)
  moreover
  have "2*(card A + card B) > 2*(card C)"
    by (metis add_less_mono assms(2) assms(3) distrib_left_numeral majority_def mult_2)
  ultimately
  show False by auto
qed

lemma majority_anti:
  fixes A B C :: "('p::finite) set"
  assumes "C \<noteq> {}" and "majority A C" and "B \<inter> A = {}"
  shows "majority A (C-B)"
  by (smt (verit, ccfv_SIG) Diff_eq Diff_subset Int_greatest assms(2) assms(3) card_mono compl_le_swap1 finite_code inf_shunt majority_def order_le_less_trans)

lemma maj_increasing:
  assumes "(A::'p::finite set) \<subseteq> B" and "B \<subseteq> X" and "\<not>majority B X"
  shows "\<not>majority A X"
proof -
  have "card A \<le> card B"
    by (simp add: assms(1) card_mono)
  thus ?thesis
    using assms unfolding majority_def by auto
qed

lemma card_maj_gt_card_not_maj:
  assumes "majority A X" and "B \<subseteq> X" and "\<not> majority B X"
  shows "card A > card B"
  by (smt (verit, ccfv_threshold) assms(1) assms(2) assms(3) linorder_neqE_nat majority_def nat_mult_less_cancel_disj order_less_subst1)

section "Definition of a round of the Non-Equivocation Model"

locale pre_round =
  fixes 
    P  \<comment> \<open>The participating set for the round\<close>
    F  \<comment> \<open>The faulty set\<close>
    C :: "('p::finite) set" \<comment> \<open>The set of participating, non-faulty processors\<close>
    and
    HO :: "'p \<Rightarrow> 'p set" \<comment> \<open>Maps each processor to the set of processors it hears of\<close>
    and
    bcast :: "'p \<Rightarrow> 'm" \<comment> \<open>@{term "bcast p = m"} means @{term p} broadcasts @{term m}.\<close>
    and
    rcvd :: "'p \<Rightarrow> 'p \<Rightarrow> 'm" \<comment> \<open>@{term "rcvd p q = m"} means @{term p} receives @{term m} from @{term q}\<close>
    and
    lambda :: 'm \<comment> \<open>Failure indication\<close>
  defines "C \<equiv> P-F"
begin

notation lambda ("\<lambda>")

end

locale round = pre_round +
  assumes
    p2:"majority C P" \<comment> \<open>majority correct\<close>
    and p3:"\<And> p p' q . \<lbrakk>q \<in> HO p; rcvd p q \<noteq> \<lambda>\<rbrakk> \<Longrightarrow> rcvd p' q \<in> {rcvd p q, \<lambda>}" \<comment> \<open>no equivocation\<close>
    and p4:"\<And> p . P-F \<subseteq> HO p" \<comment> \<open>all participating, non-faulty processors are heard of\<close>
    and p5:"\<And> p q . q \<in> C \<Longrightarrow> rcvd p q = bcast q" \<comment> \<open>messages from participating, non-faulty processors are delivered intact\<close>
    and p6:"\<And> p . HO p \<subseteq> P" \<comment> \<open>only participating processors are heard of\<close>
    and p7:"\<And> p . bcast p \<noteq> \<lambda>" \<comment> \<open>participating, non-faulty processors do not broadcast @{term \<lambda>}\<close>
    and p8:"\<And> p p' q . \<lbrakk>q \<in> HO p; rcvd p q \<noteq> \<lambda>\<rbrakk> \<Longrightarrow> q \<in> HO p'" \<comment> \<open>if @{term p} receives a non-@{term \<lambda>} message form @{term q}, then all hear from @{term q}\<close>
begin

section "Properties of the Gafni-Losa model"

lemma maj_includes_correct:
  \<comment> \<open>A majority among a heard-of set includes a correct processor\<close>
  fixes M p
  assumes "majority M (HO p)"
  obtains q where "q \<in> M \<inter> C"
proof -
  have "majority C (HO p)"
    by (metis C_def card_mono finite majority_def order_le_less_trans p2 p4 p6)
  thus ?thesis
    using majorities_intersect
    by (metis assms card.empty ex_in_conv less_nat_zero_code  majority_def mult_0_right subset_empty that)
qed

lemma maj_not_lambda:
  \<comment> \<open>If p hears of @{term m} from a majority, then @{term \<open>m \<noteq> \<lambda>\<close>}\<close>
  fixes p M m p'
  assumes "M \<subseteq> HO p"
    and "\<And> q . q \<in> M \<Longrightarrow> rcvd p q = m"
  shows "majority M (HO p) \<Longrightarrow> m \<noteq> \<lambda>"
  by (metis Int_iff assms(2) maj_includes_correct p5 p7) 

lemma ho_sets_intersect:
  fixes p p'
  shows "HO p \<inter> HO p' \<noteq> {}"
  by (metis C_def card.empty inf.absorb_iff2 inf_assoc inf_bot_left less_nat_zero_code majority_def mult_0_right p2 p4)

lemma maj_is_maj_among_hos:
  \<comment> \<open>If @{term p} receives @{term m} unanimously from a majority @{term M} then @{term M} is 
  a majority among the processors that both @{term p} and @{term p'} hear of\<close>
  fixes p M m p'
  assumes "M \<subseteq> HO p"
    and "\<And> q . q \<in> M \<Longrightarrow> rcvd p q = m"
    and "majority M (HO p)"
  shows  "majority M (HO p \<inter> HO p')"
proof -
  have "M \<inter> (HO p - HO p') = {}"
  proof -
    have "m \<noteq> \<lambda>"
      using \<open>majority M (HO p)\<close> assms(1,2) maj_not_lambda by auto
    moreover
    have "rcvd p q = \<lambda>" if "q \<in> HO p - HO p'" for q
      by (metis Diff_iff p8 that)
    ultimately show ?thesis using assms(1,2)
      by blast
  qed
  thus ?thesis using majority_anti \<open>majority M (HO p)\<close>
    by (metis Diff_Diff_Int Int_empty_left inf_aci(1))
qed

lemma faulty_min_among_hos:
  \<comment> \<open>@{term F} is a minority among the intersection of two heard-of sets\<close>
  fixes p p'
  shows "\<not>majority (F \<inter> HO p \<inter> HO p') (HO p \<inter> HO p')"
proof -
  have "majority C (HO p \<inter> HO p')"
    by (smt (verit) C_def Diff_Compl Diff_disjoint inf.absorb_iff2 inf.orderE inf_left_commute majority_anti p2 p4 p6)
  thus ?thesis
    by (metis C_def Diff_disjoint empty_subsetI inf.assoc inf.commute inf.orderE ho_sets_intersect majorities_intersect)
qed

lemma ca_lemma_2:
  \<comment> \<open>This is the most important lemma\<close>
  fixes p p' m_1 m M_1 M_1' M'
  assumes "m \<noteq> m_1" and "m \<noteq> \<lambda>"
    and "\<And> p . bcast p \<noteq> m" \<comment> \<open>processors never send @{term m}\<close>
  defines "M_1 \<equiv> {q \<in> HO p . rcvd p q = m_1}"
  assumes "majority M_1 (HO p)" \<comment> \<open>@{term p} receives @{term m_1} from a strict majority of the processors that it hears of\<close>
  defines "M_1' \<equiv> {q \<in> HO p' . rcvd p' q = m_1}"
    and "M' \<equiv> {q \<in> HO p' . rcvd p' q = m}"
  shows "card M' < card M_1'" \<comment> \<open>@{term p'} receives @{term m_1} more often than @{term m}\<close>
proof -
  have "m_1 \<noteq> \<lambda>"
    by (metis (mono_tags, lifting) CollectD M_1_def assms(5) maj_not_lambda majority_def)
  define F' where "F' \<equiv> F \<inter> HO p \<inter> HO p'"
  have "M_1 - F' \<subseteq> M_1'" unfolding M_1_def M_1'_def F'_def
    by (smt (verit, del_insts) Diff_iff IntI \<open>m_1 \<noteq> \<lambda>\<close> mem_Collect_eq round_axioms round_def subsetD subsetI)
  moreover
  have "M' \<subseteq> F' - M_1"
    unfolding M'_def M_1_def F'_def
    by (clarify, smt (verit, ccfv_threshold) C_def DiffI IntI \<open>m_1 \<noteq> \<lambda>\<close> assms(1-3) insertE mem_Collect_eq p5 p6 p8 round.p3 round_axioms singletonD subsetD)
  moreover
  have "card (F' - M_1) < card (M_1 - F')"
  proof -
    have "card F' < card M_1"
      by (metis F'_def assms(5) card_maj_gt_card_not_maj faulty_min_among_hos inf.idem inf_assoc inf_le1 inf_left_commute maj_increasing)
    thus ?thesis
      by (simp add: card_less_sym_Diff)
  qed
  ultimately 
  show ?thesis
    by (meson card_mono finite not_less order_le_less_trans)
qed

subsection "Additional properties"

lemma l2:
  \<comment> \<open>There cannot be two different unanimous majorities\<close>
  fixes p p' M m m' M'
  assumes "\<And> q . q \<in> M \<Longrightarrow> rcvd p q = m"
    and "majority M (HO p)" \<comment> \<open>p receive @{term m} from a strict majority of the processors it hears of\<close>
    and "\<And> q . q \<in> M' \<Longrightarrow> rcvd p' q = m'"
    and "majority M' (HO p')" \<comment> \<open>p' receive @{term m'} from a strict majority of the processors it hears of\<close>
  shows "m = m'"
proof -
  obtain q where "q \<in> M \<inter> M'"
  proof -
    have "majority M (HO p \<inter>HO p')"
      by (meson assms(1) assms(2) maj_is_maj_among_hos majority_def)
    moreover 
    have "majority M' (HO p \<inter> HO p')"
      using assms(4) assms(3) maj_is_maj_among_hos majority_def
      by (metis inf_commute)
    moreover have "HO p \<inter> HO p' \<noteq> {}"
      by (simp add: ho_sets_intersect)
    ultimately
    obtain q where "q \<in> M \<inter> M'"
      by (meson all_not_in_conv majorities_intersect)
    thus ?thesis ..
  qed
  moreover have "m \<noteq> \<lambda>" and "m' \<noteq> \<lambda>"
    by (metis assms(1) assms(2) maj_not_lambda majority_def, metis assms(4) assms(3) maj_not_lambda majority_def)
  moreover have "M \<subseteq> HO p"
    by (meson assms(2) majority_def)
  ultimately
  show "m = m'"
    by (metis (full_types) Int_iff assms(1) assms(3) empty_iff insert_iff p3 subsetD)
qed

lemma not_lambda:
  \<comment> \<open>one cannot receive @{term \<lambda>} from a correct processor\<close>
  fixes p q m
  assumes "q \<in> C" and "rcvd p q = m"
  shows "m \<noteq> \<lambda>"
  using C_def assms(1) assms(2) p5 p7 by auto

end

section \<open>Algorithms on blockchains\<close>

subsection \<open>Chains as partial orders\<close>

text \<open>
In this section we view chains as partial orders with bot and a no-convergence property (i.e. rooted trees).
This is the type class @{term chain_order} below. We make a few useful definition to talk about chains (conflicting,
compatible, etc.)
\<close>

context ord
begin

definition compatible where
  "compatible x y \<equiv> x \<le> y \<or> y \<le> x"

lemma compat_comm: "compatible x y = compatible y x"
  using compatible_def by auto

definition conflicting where
  "conflicting x y \<equiv> \<not>(x \<le> y \<or> y \<le> x)"

lemma conflicting_comm: "conflicting x y = conflicting y x"
  using conflicting_def by auto

lemma conflicting_is_not_compat:"conflicting x y = (\<not> compatible x y)"
  by (simp add: compatible_def conflicting_def)

end

class chain_order = order_bot +
  assumes non_convergence:"conflicting x y \<and> y \<le> v \<longrightarrow> conflicting x v"

definition tip where
  \<comment> \<open>A tip among a set of chains\<close>
  "tip m x \<equiv> x \<in> m \<and> (\<forall> y \<in> m . y \<le> x \<or> conflicting x y)"
                                  
definition most_frequent_tip :: "('a::ord) multiset \<Rightarrow> 'a \<Rightarrow> bool" where
  \<comment> \<open>A tip that is most frequent among a multi-set of chains (there is a unique such tip)\<close>
  "most_frequent_tip m x \<equiv> 
    tip (set_mset m) x \<and> (\<forall> y . y \<in># m \<and> conflicting x y \<longrightarrow> count m y < count m x)"

lemma most_frequent_tip_unique:
  fixes m and x y ::"'a::order"
  assumes "most_frequent_tip m x" and "most_frequent_tip m y"
  shows "x = y"
  by (meson assms conflicting_def dual_order.strict_trans less_irrefl_nat most_frequent_tip_def order_antisym tip_def)

definition maximally_frequent_tip :: "('a::order) multiset \<Rightarrow> 'a \<Rightarrow> bool" where
  "maximally_frequent_tip m x \<equiv> 
    tip (set_mset m) x \<and> (\<forall> y . y \<in># m \<and> conflicting x y \<longrightarrow> count m y \<le> count m x)"

subsection \<open>Specification of the second round (in the no-equivocation model) of the chain-CA algorithm\<close>

locale pre_chain_round =
  fixes
    P  \<comment> \<open>The participating set for the round\<close>
    F  \<comment> \<open>The faulty set\<close>
    C :: "('p::finite) set" \<comment> \<open>The set of participating, non-faulty processors\<close>
    and
    HO :: "'p \<Rightarrow> 'p set" \<comment> \<open>Maps each processor to the set of processors it hears of\<close>
    and
    bcast :: "'p \<Rightarrow> ('m::chain_order)" \<comment> \<open>@{term "bcast p = m"} means @{term p} broadcasts @{term m}\<close>
    and
    rcvd :: "'p \<Rightarrow> 'p \<Rightarrow> 'm option" \<comment> \<open>@{term "rcvd p q = Some m"} means @{term p} receives @{term m} from @{term q}\<close>
  defines "C \<equiv> P-F"

locale chain_round = pre_chain_round +
  assumes 
    p2:"majority C P" \<comment> \<open>majority of correct processes\<close>
    and p3:"\<And> p p' q . \<lbrakk>q \<in> HO p; rcvd p q \<noteq> None\<rbrakk> \<Longrightarrow> rcvd p' q \<in> {rcvd p q, None}" \<comment> \<open>no equivocation\<close>
    and p4:"\<And> p . P-F \<subseteq> HO p" \<comment> \<open>all participating, non-faulty processors are heard of\<close>
    and p5:"\<And> p q . q \<in> C \<Longrightarrow> rcvd p q = Some (bcast q)" \<comment> \<open>messages from participating, non-faulty processors are delivered intact\<close>
    and p6:"\<And> p . HO p \<subseteq> P" \<comment> \<open>only participating processors are heard of\<close>
    and p8:"\<And> p p' q . \<lbrakk>q \<in> HO p; rcvd p q \<noteq> None\<rbrakk> \<Longrightarrow> q \<in> HO p'" \<comment> \<open>if @{term p} receives a message form @{term q}, then all hear from @{term q}\<close>
begin

subsection \<open>The main lemma\<close>

lemma maj_includes_correct:
  \<comment> \<open>A majority among a heard-of set includes a correct processor\<close>
  fixes M p
  assumes "majority M (HO p)"
  obtains q where "q \<in> M \<inter> C"
proof -
  have "majority C (HO p)"
    by (metis C_def card_mono finite majority_def order_le_less_trans p2 p4 p6)
  thus ?thesis
    using majorities_intersect
    by (metis assms card.empty ex_in_conv less_nat_zero_code  majority_def mult_0_right subset_empty that)
qed

lemma maj_not_None:
  fixes p M m p'
  assumes "M \<subseteq> HO p"
    and "\<And> q . q \<in> M \<Longrightarrow> rcvd p q = m"
  shows "majority M (HO p) \<Longrightarrow> m \<noteq> None"
  by (metis Int_iff assms(2) maj_includes_correct option.distinct(1) p5)

lemma maj_is_maj_among_hos:
  \<comment> \<open>If @{term M} is a majority among the processes that @{term p} receives a value from, then it is 
  a majority among the processors that both @{term p} and @{term p'} hear of\<close>
  fixes p M m p'
  assumes "M \<subseteq> HO p"
    and "\<And> q . q \<in> M \<Longrightarrow> rcvd p q \<noteq> None"
    and "majority M (HO p)"
  shows  "majority M (HO p \<inter> HO p')"
proof -
  have "M \<inter> (HO p - HO p') = {}"
    using assms(2) p8 by fastforce
  thus ?thesis using majority_anti \<open>majority M (HO p)\<close>
    by (metis Diff_Diff_Int Int_empty_left inf_aci(1))
qed

lemma ho_sets_intersect:
  fixes p p'
  shows "HO p \<inter> HO p' \<noteq> {}"
  by (metis C_def card.empty inf.absorb_iff2 inf_assoc inf_bot_left less_nat_zero_code majority_def mult_0_right p2 p4)

lemma faulty_min_among_hos:
  \<comment> \<open>@{term F} is a minority among the intersection of two heard-of sets\<close>
  fixes p p'
  shows "\<not>majority (F \<inter> HO p \<inter> HO p') (HO p \<inter> HO p')"
proof -
  have "majority C (HO p \<inter> HO p')"
    by (smt (verit) C_def Diff_Compl Diff_disjoint inf.absorb_iff2 inf.orderE inf_left_commute majority_anti p2 p4 p6)
  thus ?thesis
    by (metis C_def Diff_disjoint empty_subsetI inf.assoc inf.commute inf.orderE ho_sets_intersect majorities_intersect)
qed

lemma chain_ca_lemma:
  \<comment> \<open>This is the main lemma\<close>
  fixes p :: "'a::finite"
    and p' :: "'a::finite"
    and x :: "'b::chain_order" 
    and y :: "'b::chain_order"
  assumes "conflicting x y"
    and "\<And> p . compatible (bcast p) x" \<comment> \<open>processors only bcast values compatible with @{term x}\<close>
  defines "X \<equiv> {q \<in> HO p . \<exists> v . rcvd p q = Some v \<and> x \<le> v}"
  assumes "majority X (HO p)" \<comment> \<open>@{term p} receives an extension of @{term x} from a strict majority of the processors that it hears of\<close>
  defines "X' \<equiv> {q \<in> HO p' . \<exists> v . rcvd p' q = Some v \<and> x \<le> v}"
  defines "Y' \<equiv> {q \<in> HO p' . \<exists> v . rcvd p' q = Some v \<and> y \<le> v}"
  shows "card Y' < card X'" \<comment> \<open>@{term p'} receives an extension of @{term x} more often than it receives an extension of @{term y}\<close>
  (*nitpick[verbose, card 'a=3, card 'b=3, card nat=10, card "'a list" = 20, bits=6]*)
proof -

  define A 
    \<comment> \<open>We start by defining the set @{term A} of processors among @{term X} from which @{term p'} 
receives either a value that conflicts with @{term x} or the failure indication.\<close>
    where "A \<equiv> {q \<in> HO p . \<exists> v . rcvd p q = Some v \<and> x \<le> v 
      \<and> (rcvd p' q = None \<or> (\<exists> v . rcvd p' q = Some v \<and> conflicting v x))}"

  have "X-A \<subseteq> X'"
    unfolding X_def X'_def A_def
    apply auto
     apply (metis option.distinct(1) p8)
    apply (metis insertE option.distinct(1) option.inject p3 singletonD)
    done
  moreover
  have "A \<inter> Y' = {}" 
    unfolding A_def Y'_def
    by (auto; metis conflicting_def insertE option.distinct(1) option.inject p3 singletonD)
  ultimately
  have "card X' - card Y' \<ge> card X - card (Y' \<union> A)"
    by (smt (verit, del_insts) add.commute card_Un_disjoint card_mono diff_card_le_card_Diff diff_diff_left diff_le_mono disjoint_iff_not_equal finite le_trans)

  have "A \<union> Y' \<subseteq> F \<inter> HO p \<inter> HO p'"
  proof -
    have "A \<union> Y' \<subseteq> F"
      unfolding A_def Y'_def
      apply auto
        apply (metis C_def DiffI option.distinct(1) p5 p6 subsetD)
       apply (metis C_def DiffI conflicting_def option.sel p5 p6 subsetD)
      apply (metis C_def DiffI assms(1) assms(2) conflicting_comm conflicting_is_not_compat non_convergence option.sel p5 p6 subsetD)
      done
    moreover
    have "A \<subseteq> HO p \<inter> HO p'"
      using A_def p8 by fastforce
    moreover
    have "Y' \<subseteq> HO p \<inter> HO p'"
      using Y'_def p8 by fastforce 
    ultimately
    show ?thesis
      by blast 
  qed

  have "majority X (HO p \<inter> HO p')"
    unfolding X_def using maj_is_maj_among_hos
    by (smt (verit, best) X_def assms(4) majority_def mem_Collect_eq option.distinct(1))
  moreover 
  have  "\<not>majority (A \<union> Y') (HO p \<inter> HO p')"
    using \<open>A \<union> Y' \<subseteq> F \<inter> HO p \<inter> HO p'\<close> maj_increasing faulty_min_among_hos
    by (metis inf_assoc inf_le2)
  ultimately have "card X > card (A \<union> Y')"
    by (meson \<open>A \<union> Y' \<subseteq> F \<inter> HO p \<inter> HO p'\<close> card_maj_gt_card_not_maj le_inf_iff)

  show ?thesis
    by (metis \<open>card (A \<union> Y') < card X\<close> \<open>card X - card (Y' \<union> A) \<le> card X' - card Y'\<close> gr0I linorder_not_le sup_commute zero_less_diff)
qed

end

section "MMR"

text \<open>
Here we want to model and prove correct the MMR algorithm.
\<close>

locale pre_mmr =
  fixes
    P :: "nat \<Rightarrow> ('p::finite) set" \<comment> \<open>The participating set for each the round\<close>
    and
    F :: "nat \<Rightarrow> 'p set" \<comment> \<open>The faulty set for each round\<close>
    and
    C :: "nat \<Rightarrow> 'p set" \<comment> \<open>The set of participating, non-faulty processors\<close>
    and
    HO :: "nat \<Rightarrow> 'p \<Rightarrow> 'p set" \<comment> \<open>Maps each processor to the set of processors it hears of in each round\<close>
    and
    bcast :: "nat \<Rightarrow> 'p \<Rightarrow> ('m::chain_order)" \<comment> \<open>@{term "bcast i p = m"} means @{term p} broadcasts @{term m} in round @{term i}\<close>
    and
    rcvd :: "nat \<Rightarrow> 'p \<Rightarrow> 'p \<Rightarrow> 'm option" \<comment> \<open>@{term "rcvd i p q = Some m"} means @{term p} receives @{term m} from @{term q} in round @{term i}\<close>
  defines "C \<equiv> P-F"

end