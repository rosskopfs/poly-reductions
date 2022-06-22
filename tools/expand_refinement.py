import pyperclip
import re
from textwrap import dedent


class LetFun:
    def __get_let_body(self, def_name):
        start, end = 0, 0
        for index, line in enumerate(self.input):
            if re.match("definition \"" + def_name, line):
                start = index + 2
            if start != 0 and re.match("^ *in[ *|$]", line):
                end = index
                break
        return self.input[start:end]

    def __load_subprograms(self):
        for sub in self.subprograms:
            self.subprograms[sub] = self.__get_let_body(sub)

    def __build_let_fun(self):
        return dedent('''\
            function {let_fun_name}::
              "{record} \\<Rightarrow> {record}" where
              "{let_fun_name} s =
              (if {loop_condition} s \\<noteq> 0
               then
                let next_iteration = {let_fun_name} ({state_upd} s)
                in next_iteration
               else
                let ret = {after_loop} s
                in ret
              )"
              by simp+
            termination
              apply (relation "measure <?>")
              apply (simp add: {subprogram_simps})+
              done

            declare {let_fun_name}.simps [simp del]
            '''.format(let_fun_name=self.ref_name + "_imp", record=self.ref_name + "_state",
                       loop_condition=self.ref_name + "_imp_compute_loop_condition",
                       state_upd=self.ref_name + "_state_upd",
                       after_loop=self.ref_name + "_imp_after_loop",
                       subprogram_simps=self.ref_name + "_imp_subprogram_simps"))

    def __build_sub_simps_lemma(self):
        sub_simps = f'lemmas {self.ref_name + "_imp_subprogram_simps"} = \n'
        for sub_def in [s + "_def" for s in self.subprograms]:
            sub_simps += f"  {sub_def}\n"
        return sub_simps

    def __build_let_fun_correct_lemma(self):
        return dedent('''\
            lemma {lemma_name}:
              "{state_ret_fun} ({let_fun_name} s) =
                {ref_name} <?arguments>"
              apply (induction s rule: {let_fun_name}.induct)
              apply (subst {let_fun_name}.simps)
              apply (subst {ref_name}.simps)
              apply (simp del: {ref_name}.simps add: {subprogram_simps} Let_def)
              done\
            '''.format(lemma_name=self.ref_name + "_imp_correct",
                       state_ret_fun=self.ref_name + "_ret",
                       let_fun_name=self.ref_name + "_imp",
                       ref_name=self.ref_name,
                       subprogram_simps=self.ref_name + "_imp_subprogram_simps"))

    def __init__(self, input, ref_name) -> None:
        self.input = input
        self.ref_name = ref_name
        self.subprograms = {self.ref_name + s: () for s in ["_state_upd",  # TODO: rename to imp_state_upd
                                                            "_imp_compute_loop_condition",
                                                            "_imp_after_loop"]}
        self.__load_subprograms()
        self.imp_function = self.__build_let_fun()
        self.lemmas = {
            self.ref_name + "_imp_subprogram_simps": self.__build_sub_simps_lemma(),
            self.ref_name + "_imp_correct": self.__build_let_fun_correct_lemma()
        }

    def output(self):
        return "\n".join([self.lemmas[self.ref_name + "_imp_subprogram_simps"], self.imp_function,
                          self.lemmas[self.ref_name + "_imp_correct"]])


class LetTimeFun:
    def __build_def(self, original_name):
        defn = f"definition \"{original_name}_time t s \\<equiv>\n  let\n"
        for index, line in enumerate(self.let_fun.subprograms[original_name]):
            defn += line
            if not index == len(self.let_fun.subprograms[original_name]) - 1:
                next_line = self.let_fun.subprograms[original_name][index + 1]
            if index == len(self.let_fun.subprograms[original_name]) - 1 or not next_line[4] == ' ':
                defn += "\n    t = t + ;\n"
            else:
                defn += "\n"
        defn += "  in\n    ret\n\""
        return defn

    def __build_subprogram_defs(self):
        for sub in self.let_fun.subprograms:
            self.subprograms[sub + "_time"] = self.__build_def(sub)

    def __build_sub_simps_lemma(self):
        sub_simps = f"lemmas {self.let_fun.ref_name}_imp_subprogram_time_simps = \n"
        for sub_def in [s + "_def" for s in self.subprograms]:
            sub_simps += f"  {sub_def}\n"
        sub_simps += f"  {self.let_fun.ref_name}_imp_subprogram_simps\n"
        return sub_simps

    def __build_let_time_fun(self):
        return dedent('''\
            function {let_fun_name}::
              "nat \\<Rightarrow> {record} \\<Rightarrow> nat" where
              "{let_fun_name} t s =
              {loop_condition_time} 0 s +
              (if {loop_condition} s \\<noteq> 0
                then
                  (let
                    t = t + 1;
                    next_iteration =
                      {let_fun_name} (t + {state_upd_time} 0 s)
                                     ({state_upd} s)
                   in next_iteration)
                else
                  (let
                    t = t + 2;
                    ret = t + {after_loop} 0 s
                   in ret)
              )"
              by auto
            termination
              apply (relation "measure (<?> \\<circ> snd)")
              by (simp add: {subprogram_simps})+
              done

            declare {let_fun_name}.simps [simp del]\
            '''.format(let_fun_name=self.let_fun.ref_name + "_imp_time",
                       record=self.let_fun.ref_name + "_state",
                       loop_condition_time=self.let_fun.ref_name + "_imp_compute_loop_condition_time",
                       loop_condition=self.let_fun.ref_name + "_imp_compute_loop_condition",
                       state_upd=self.let_fun.ref_name + "_state_upd",
                       state_upd_time=self.let_fun.ref_name + "_state_upd_time",
                       after_loop=self.let_fun.ref_name + "_imp_after_loop_time",
                       subprogram_simps=self.let_fun.ref_name + "_imp_subprogram_time_simps"))

    def __build_time_acc_lemma(self):
        return dedent('''\
            lemma {lem_name}:
              "({time_imp} (Suc t) s) = Suc ({time_imp} t s)"
              by (induction t s rule: {time_imp}.induct)
                ((subst (1 2) {time_imp}.simps);
                  (simp add: {state_upd}))\
            '''.format(lem_name=self.let_fun.ref_name + "_imp_time_acc",
                       time_imp=self.let_fun.ref_name + "_imp_time",
                       state_upd=self.let_fun.ref_name + "_state_upd_def"))

    def __build_time_acc_lemma_2_aux(self):
        return dedent('''\
            lemma {lem_name}:
              "({time_imp} t s) = t + ({time_imp} 0 s)"
              by (induction t arbitrary: s) (simp add: {time_acc})+\
            '''.format(lem_name=self.let_fun.ref_name + "_imp_time_acc_2_aux",
                       time_imp=self.let_fun.ref_name + "_imp_time",
                       time_acc=self.let_fun.ref_name + "_imp_time_acc"))

    def __build_time_acc_lemma_2(self):
        return dedent('''\
            lemma {lem_name}:
              "t \\<noteq> 0 \\<Longrightarrow> ({time_imp} t s) = t + ({time_imp} 0 s)"
              by (rule {rule})\
            '''.format(lem_name=self.let_fun.ref_name + "_imp_time_acc_2",
                       time_imp=self.let_fun.ref_name + "_imp_time",
                       rule=self.let_fun.ref_name + "_imp_time_acc_2_aux"))

    def __build_time_acc_lemma_3(self):
        return dedent('''\
            lemma {lem_name}:
              "({time_imp} (a + b) s) = a + ({time_imp} b s)"
              by (induction a arbitrary: b s) (simp add: {time_acc})+\
            '''.format(lem_name=self.let_fun.ref_name + "_imp_time_acc_3",
                       time_imp=self.let_fun.ref_name + "_imp_time",
                       time_acc=self.let_fun.ref_name + "_imp_time_acc"))

    def __init__(self, input, ref_name) -> None:
        self.let_fun = LetFun(input, ref_name)
        self.subprograms = {s + "_time": () for s in self.let_fun.subprograms}
        self.__build_subprogram_defs()
        self.lemmas = {
            self.let_fun.ref_name + "_imp_subprogram_time_simps": self.__build_sub_simps_lemma(),
            self.let_fun.ref_name + "_imp_time_acc": self.__build_time_acc_lemma(),
            self.let_fun.ref_name + "_imp_time_acc_2_aux": self.__build_time_acc_lemma_2_aux(),
            self.let_fun.ref_name + "_imp_time_acc_2": self.__build_time_acc_lemma_2(),
            self.let_fun.ref_name + "_imp_time_acc_3": self.__build_time_acc_lemma_3()
        }

    def output(self):
        return "\n".join([self.subprograms[sub] + "\n" for sub in self.subprograms] +
                         [self.lemmas[self.let_fun.ref_name + "_imp_subprogram_time_simps"],
                         self.__build_let_time_fun() + "\n"] +
                         [self.lemmas[lemma] + "\n" for lemma in self.lemmas
                         if not lemma == self.let_fun.ref_name + "_imp_subprogram_time_simps"])


class ImpFun:
    def __set_comment(self, lines):
        open_str = "\\<comment> \\<open>"
        close_str = "\\<close>"

        commented_lines = []
        for line in lines:
            commented_lines += ["  " + open_str + line[4:] + close_str]

        return commented_lines

    def __build_func_lemma(self):
        return dedent('''\
        lemma {name}_IMP_Minus_correct_function:
          "(invoke_subprogram p {name}_IMP_Minus, s) \\<Rightarrow>\\<^bsup>t\\<^esup> s' \\<Longrightarrow>
             s' (add_prefix p {name}_ret_str)
              = {name}_ret
                  ({name}_imp ({name}_imp_to_HOL_state p s))"
          apply(induction "{name}_imp_to_HOL_state p s" arbitrary: s s' t
            rule: {name}_imp.induct)
          apply(subst {name}_imp.simps)
          apply(simp only: {name}_IMP_Minus_def prefix_simps)
          apply(erule Seq_E)+
          apply(erule While_tE)

          subgoal
            apply(simp only: {name}_IMP_subprogram_simps prefix_simps)
            apply(erule Seq_E)+
            apply(erule <?>_IMP_Minus_correct[where vars = "{name}_IMP_vars"])
            subgoal premises p using p(999) by fastforce
            by(fastforce simp: {name}_IMP_subprogram_simps
                {name}_imp_subprogram_simps
                {name}_state_translators)

          apply(erule Seq_E)+
          apply(dest_com_gen)

          subgoal
              apply(simp only: {name}_IMP_init_while_cond_def prefix_simps)
              apply(erule Seq_E)+
              apply(erule <?>_IMP_Minus_correct[where vars = "{name}_IMP_vars"])
              subgoal premises p using p(999) by fastforce
              by(fastforce simp add: {name}_complete_simps)

          subgoal
              apply(subst (asm) {name}_IMP_init_while_cond_def)
              apply(simp only: {name}_IMP_loop_body_def prefix_simps)
              apply(erule Seq_E)+
              apply(erule <?>_IMP_Minus_correct[where vars = "{name}_IMP_vars"])
              subgoal premises p using p(999) by fastforce
              by (simp only: {name}_imp_subprogram_simps
                  {name}_state_translators Let_def, force)

          subgoal
              apply(simp only: {name}_IMP_init_while_cond_def prefix_simps
                  {name}_IMP_loop_body_def)
              apply(erule Seq_E)+
              apply(erule <?>_IMP_Minus_correct[where vars = "{name}_IMP_vars"])
              subgoal premises p using p(999) by fastforce
              by (simp only: {name}_imp_subprogram_simps
                  {name}_state_translators Let_def, force)
          done\
        '''.format(name=self.let_fun.ref_name)).splitlines()

    def __build_time_lemma(self):
        return dedent('''\
        lemma {name}_IMP_Minus_correct_time:
          "(invoke_subprogram p {name}_IMP_Minus, s) \\<Rightarrow>\\<^bsup>t\\<^esup> s' \\<Longrightarrow>
             t = {name}_imp_time 0 ({name}_imp_to_HOL_state p s)"
          apply(induction "{name}_imp_to_HOL_state p s" arbitrary: s s' t
              rule: {name}_imp.induct)
          apply(subst {name}_imp_time.simps)
          apply(simp only: {name}_IMP_Minus_def prefix_simps)

          apply(erule Seq_tE)+
          apply(erule While_tE_time)

          subgoal
            apply(simp only: {name}_IMP_subprogram_simps prefix_simps)
            apply(erule Seq_tE)+
            apply(erule <?>_IMP_Minus_correct[where vars = "{name}_IMP_vars"])
            subgoal premises p using p(999) by fastforce
            by (force simp: {name}_IMP_subprogram_simps
                {name}_imp_subprogram_time_simps {name}_state_translators)

          apply(erule Seq_tE)+
          apply(simp add: add.assoc)
          apply(dest_com_gen_time)

          subgoal
            apply(simp only: {name}_IMP_init_while_cond_def prefix_simps)
            apply(erule Seq_tE)+
            apply(erule <?>_IMP_Minus_correct[where vars = "{name}_IMP_vars"])
            subgoal premises p using p(999) by fastforce
            by(fastforce simp add: {name}_complete_simps)

          subgoal
            apply(subst (asm) {name}_IMP_init_while_cond_def)
            apply(simp only: {name}_IMP_loop_body_def prefix_simps)
            apply(erule Seq_tE)+
            apply(erule <?>_IMP_Minus_correct[where vars = "{name}_IMP_vars"])
            subgoal premises p using p(999) by fastforce
            by (simp only: {name}_imp_subprogram_time_simps
                {name}_state_translators Let_def, force)

          subgoal
            apply(simp only: prefix_simps {name}_IMP_init_while_cond_def
                {name}_IMP_loop_body_def)
            apply(erule Seq_tE)+
            apply(erule <?>_IMP_Minus_correct[where vars = "{name}_IMP_vars"])
            subgoal premises p using p(999) by fastforce
            apply(simp only: {name}_complete_time_simps Let_def)
            by force

          done\
        '''.format(name=self.let_fun.ref_name)).splitlines()

    def __init__(self, input, ref_name) -> None:
        self.let_fun = LetFun(input, ref_name)

        self.definitions = {
            self.let_fun.ref_name + "_while_cond":
            [f"abbreviation \"{self.let_fun.ref_name}_while_cond \\<equiv> ''condition''\""],
            self.let_fun.ref_name + "_IMP_init_while_cond":
            [f"definition \"{self.let_fun.ref_name}_IMP_init_while_cond \\<equiv>"] +
                self.__set_comment(self.let_fun.subprograms[self.let_fun.ref_name +
                                                            "_imp_compute_loop_condition"]) +
            ["  Com.SKIP", "\""],
            self.let_fun.ref_name + "_IMP_loop_body":
            [f"definition \"{self.let_fun.ref_name}_IMP_loop_body \\<equiv>"] +
                self.__set_comment(self.let_fun.subprograms[self.let_fun.ref_name +
                                                            "_state_upd"]) +
            ["  Com.SKIP", "\""],
            self.let_fun.ref_name + "_IMP_after_loop":
            [f"definition \"{self.let_fun.ref_name}_IMP_after_loop \\<equiv>"] +
                self.__set_comment(self.let_fun.subprograms[self.let_fun.ref_name +
                                                            "_imp_after_loop"]) +
            ["  Com.SKIP", "\""],
            self.let_fun.ref_name + "_IMP_Minus":
            [f"definition {self.let_fun.ref_name}_IMP_Minus where",
             f"  \"{self.let_fun.ref_name}_IMP_Minus \\<equiv>",
             f"  {self.let_fun.ref_name}_IMP_init_while_cond;;",
             f"  WHILE {self.let_fun.ref_name}_while_cond \\<noteq>0 DO (",
             f"    {self.let_fun.ref_name}_IMP_loop_body;;",
             f"    {self.let_fun.ref_name}_IMP_init_while_cond",
             "  );;",
             f"  {self.let_fun.ref_name}_IMP_after_loop\""],
            self.let_fun.ref_name + "_IMP_vars":
            [f"abbreviation \"{self.let_fun.ref_name}_IMP_vars\\<equiv>",
             "  {}\""],
            self.let_fun.ref_name + "_IMP_subprogram_simps":
            [f"lemmas {self.let_fun.ref_name}_IMP_subprogram_simps =",
             f"  {self.let_fun.ref_name}_IMP_init_while_cond_def",
             f"  {self.let_fun.ref_name}_IMP_loop_body_def",
             f"  {self.let_fun.ref_name}_IMP_after_loop_def"],
            self.let_fun.ref_name + "_imp_to_HOL_state":
            [f"definition \"{self.let_fun.ref_name}_imp_to_HOL_state p s =",
             f"  \\<lparr>{self.let_fun.ref_name}<?> = (s (add_prefix p {self.let_fun.ref_name}<?>)),",
             f"   {self.let_fun.ref_name}<?> = (s (add_prefix p {self.let_fun.ref_name}<?>))\\<rparr>\""],
            self.let_fun.ref_name + "_state_translators":
            [f"lemmas {self.let_fun.ref_name}_state_translators =",
             f"  {self.let_fun.ref_name}_imp_to_HOL_state_def"],
            self.let_fun.ref_name + "_complete_simps":
            [f"lemmas {self.let_fun.ref_name}_complete_simps =",
             f"  {self.let_fun.ref_name}_IMP_subprogram_simps",
             f"  {self.let_fun.ref_name}_imp_subprogram_simps",
             f"  {self.let_fun.ref_name}_state_translators"],
            self.let_fun.ref_name + "_IMP_Minus_correct_function": self.__build_func_lemma(),
            self.let_fun.ref_name + "_IMP_Minus_correct_effects":
            dedent('''\
            lemma {name}_IMP_Minus_correct_effects:
              "\\<lbrakk>(invoke_subprogram (p @ {name}_pref) {name}_IMP_Minus, s) \\<Rightarrow>\\<^bsup>t\\<^esup> s';
                v \\<in> vars; \\<not> (prefix {name}_pref v)\\<rbrakk>
               \\<Longrightarrow> s (add_prefix p v) = s' (add_prefix p v)"
              using com_add_prefix_valid'' com_only_vars prefix_def
              by blast\
            '''.format(name=self.let_fun.ref_name)).splitlines(),
            self.let_fun.ref_name + "_complete_time_simps":
            [f"lemmas {self.let_fun.ref_name}_complete_time_simps =",
             f"  {self.let_fun.ref_name}_imp_subprogram_time_simps",
             f"  {self.let_fun.ref_name}_imp_time_acc",
             f"  {self.let_fun.ref_name}_imp_time_acc_2",
             f"  {self.let_fun.ref_name}_imp_time_acc_3",
             f"  {self.let_fun.ref_name}_state_translators"],
            self.let_fun.ref_name + "_IMP_Minus_correct_time": self.__build_time_lemma(),
            self.let_fun.ref_name + "_IMP_Minus_correct":
            dedent('''\
            lemma {name}_IMP_Minus_correct:
              "\\<lbrakk>(invoke_subprogram (p1 @ p2) {name}_IMP_Minus, s) \\<Rightarrow>\\<^bsup>t\\<^esup> s';
                \\<And>v. v \\<in> vars \\<Longrightarrow> \\<not> (set p2 \\<subseteq> set v);
                \\<lbrakk>t = ({name}_imp_time 0 ({name}_imp_to_HOL_state (p1 @ p2) s));
                 s' (add_prefix (p1 @ p2) {name}_ret_str) =
                      {name}_ret ({name}_imp
                                                    ({name}_imp_to_HOL_state (p1 @ p2) s));
                 \\<And>v. v \\<in> vars \\<Longrightarrow> s (add_prefix p1 v) = s' (add_prefix p1 v)\\<rbrakk>
               \\<Longrightarrow> P\\<rbrakk> \\<Longrightarrow> P"
              using {name}_IMP_Minus_correct_function
              by (auto simp: {name}_IMP_Minus_correct_time)
                (meson {name}_IMP_Minus_correct_effects set_mono_prefix)\
                        '''.format(name=self.let_fun.ref_name)).splitlines()
        }

    def output(self):
        return "\n\n".join(["\n".join(val) for val in self.definitions.values()])


class Refinement:
    def __set_name(self):
        for line in self.input:
            search = re.search("definition \"(.*)_state_upd", line)
            if search:
                self.name = search.group(1)
                return

    def __set_var_names(self):
        self.vars = []
        for line in self.input:
            search = re.search("abbreviation \"(.*_str) ", line)
            if search:
                self.vars.append(search.group(1))

    def __init__(self, input) -> None:
        self.input = input
        self.__set_name()
        self.__set_var_names()


# with open(r"tools\test-input.txt", encoding='UTF-8') as f:
#     input = f.read().splitlines()

inp = pyperclip.paste().splitlines()

foo = Refinement(inp)
bar = LetFun(inp, foo.name)
baz = LetTimeFun(inp, foo.name)
imp = ImpFun(inp, foo.name)

print(bar.output() + "\n\n" + baz.output() + "\n" + imp.output())
