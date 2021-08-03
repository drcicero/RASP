from antlr4 import CommonTokenStream, InputStream
from collections.abc import Iterable

from zzantlr.RASPLexer import RASPLexer
from zzantlr.RASPParser import RASPParser

from Environment import Environment, UndefinedVariable, ReservedName
from FunctionalSupport import UnfinishedSequence, UnfinishedSelect, Unfinished
from Evaluator import Evaluator, NamedVal, RASPFunction, ArgsError, RASPTypeError, RASPValueError
from Support import Select, Sequence, lazy_type_check

from typing import Union

encoder_name = "s-op"

debug = False

def debprint(*a,**kw):
	if debug:
		print(*a,**kw)

class ReturnExample:
	def __init__(self,subset):
		self.subset = subset

class LoadError(Exception):
	def __init__(self,msg):
		super().__init__(msg)

def is_comment(line):
	if not isinstance(line,str):
		return False
	return line.strip().startswith("#")

def formatstr(res):
	if isinstance(res,str):
		return "\""+res+"\""
	return str(res)

class REPL:
	__slots__ = ["env","sequence_running_example","selector_running_example","sequence_prints_verbose",
	             "show_sequence_examples","show_selector_examples","printing", "print_buffer", "base_env"]

	def __init__(self):
		self.env = Environment(name="console")
		self.sequence_running_example = "hello"
		self.selector_running_example = "hello"
		self.sequence_prints_verbose = False
		self.show_sequence_examples = True
		self.show_selector_examples = True
		self.printing = True
		self.print_buffer: list[Union[NamedVal, str]] = []
		self.base_env = None

		self.print_welcome()
		self.load_base_libraries_and_make_base_env()

	def load_base_libraries_and_make_base_env(self):
		self.base_env = self.env.snapshot() # base env: the env from which every load begins
		# bootstrap base_env with current (basically empty except indices etc) env, then load
		# the base libraries to build the actual base env
		for l in ["RASP_support/rasplib"]:
			tmp, self.printing = self.printing, False
			_ = self.run_tree(None,"load \""+l+"\";",self.env)
			self.base_env = self.env.snapshot()
			self.printing = tmp
			for i,r in enumerate(self.print_buffer):
				if isinstance(r, NamedVal):
					self.print_buffer[i] = None
			self.flush()

	def set_running_example(self,example,which):
		if which in ["both",encoder_name]:
			self.sequence_running_example = example
		if which in ["both","selector"]:
			self.selector_running_example = example

	def print_welcome(self):
		print("RASP 0.0")
		print("running example is:",self.sequence_running_example)

	def print_named_val(self,name,val,ntabs=0,extra_first_pref=""):
		if (None is name) and isinstance(val,Unfinished):
			name = val.name
		pref="\t"*ntabs
		if None is val:
			return
		elif isinstance(val,Select):
			print(pref," = ")
			print_select(val.created_from_input,val)
		elif isinstance(val,Sequence) and self.sequence_prints_verbose:
			print(pref," = ",end="")
			print_seq(val.created_from_input,val,still_on_prev_line=True)
		elif isinstance(val,UnfinishedSequence):
			print(pref,extra_first_pref,"   "+encoder_name+":",name)
			if self.show_sequence_examples:
				if self.sequence_prints_verbose:
					print(pref,"\t Example:",end="")
					optional_exampledesc = name+"("+formatstr(self.sequence_running_example)+") ="
					print_seq(self.selector_running_example,val(self.sequence_running_example),still_on_prev_line=True,
										extra_pref=pref,lastpref_if_shortprint=optional_exampledesc)
				else:
					print(pref,"\t Example:",name+"("+formatstr(self.sequence_running_example)+\
						") =",val(self.sequence_running_example))
		elif isinstance(val,UnfinishedSelect):
			print(pref,extra_first_pref,"   selector:",name)
			if self.show_selector_examples:
				print(pref,"\t Example:")#,name+"("+formatstr(self.selector_running_example)+") =")
				print_select(self.selector_running_example,val(self.selector_running_example),extra_pref=pref)
		elif isinstance(val,RASPFunction):
			print(pref,extra_first_pref,"   "+str(val))
		elif isinstance(val,list):
			named = "   list: "+((name+" = ") if None is not name else "")
			print(pref,extra_first_pref,named,end="")
			flat = not any(isinstance(v,(list,dict,Unfinished)) for v in val)
			if flat:
				print(val)
			else:
				print(pref,"[")
				for v in val:
					self.print_named_val(None,v,ntabs=ntabs+2)
				print(pref," "*len(named),"]")
		elif isinstance(val,dict):
			named = "   dict: "+((name+" = ") if None is not name else "")
			print(pref,extra_first_pref,named,end="")
			flat = not any(isinstance(val[v],(list,dict,Unfinished)) for v in val)
			if flat:
				print(val)
			else:
				print(pref,"{")
				for v in val:
					self.print_named_val(None,val[v],ntabs=ntabs+3,extra_first_pref=formatstr(v)+" : ")
				print(pref," "*len(named),"}")
		else:
			print(pref,(("   value: "+name+" = ") if name not in [None, "", "out"] else "= "),formatstr(val).replace("\n","\n\t\t\t"))

	def print_example(self,nres):
		if nres.subset in ["both",encoder_name]:
			print("\t"+encoder_name+" example:",formatstr(self.sequence_running_example))
		if nres.subset in ["both","selector"]:
			print("\tselector example:",formatstr(self.selector_running_example))

	def print_result(self,rp):
		if rp is None:
			return
		elif isinstance(rp, str):
			print(rp)
		elif isinstance(rp,NamedVal):
			self.print_named_val(rp.name,rp.val)
		elif isinstance(rp,ReturnExample):
			self.print_example(rp)
		elif debug:
			raise TypeError("something went wrong, wrong type in result_to_print -- ", rp)
		else:
			print("something went wrong, wrong type in result_to_print -- ", rp)

	def evaluate_replstatement(self,ast):
		if ast.setExample():
			return self.setExample(ast.setExample())
		elif ast.showExample():
			return self.showExample(ast.showExample())
		elif ast.toggleExample():
			return self.toggleExample(ast.toggleExample())
		elif ast.toggleSeqVerbose():
			return self.toggleSeqVerbose(ast.toggleSeqVerbose())
		elif ast.exit():
			raise EOFError
		else:
			if debug:
				raise NotImplemented
			print("something went wrong, wrong type in result_to_print -- ", ast)

	def toggleSeqVerbose(self,ast):
		switch = ast.switch.text
		self.sequence_prints_verbose = switch == "on"

	def toggleExample(self,ast):
		subset = ast.subset
		subset = "both" if not subset else subset.text
		switch = ast.switch.text
		examples_on = switch=="on"
		if subset in ["both",encoder_name]:
			self.show_sequence_examples = examples_on
		if subset in ["both","selector"]:
			self.show_selector_examples = examples_on

	def showExample(self,ast):
		subset = ast.subset
		subset = "both" if not subset else subset.text
		return ReturnExample(subset)

	def setExample(self,ast):
		example = Evaluator(self.env,self).evaluateExpr(ast.example).val
		if not isinstance(example,Iterable):
			raise RASPTypeError("example not iterable: "+str(example))
		subset = ast.subset
		subset = "both" if not subset else subset.text
		self.set_running_example(example,subset)
		#return ReturnExample(subset)
		return None # dont print anything

	def loadFile(self,ast,calling_env) -> None:
#		if None is calling_env:
#			calling_env = self.env
		libname = ast.filename.text[1:-1]
		filename = libname + ".rasp"
		try:
			with open(filename,"r") as f:
				tmp1, tmp2, tmp3, self.show_sequence_examples, self.show_selector_examples, self.printing = \
					self.show_sequence_examples, self.show_selector_examples, self.printing, False, False, False
				self.run(fromfile=f,env=Environment(name=libname,parent_env=self.base_env,stealing_env=calling_env))
				self.printing = tmp3
				self.flush()
				self.show_sequence_examples, self.show_selector_examples = tmp1, tmp2
		except FileNotFoundError:
			raise LoadError("could not find file: "+filename)

	def run_tree(self,fromfile,fromline,env) -> bool:
		try:
			tree = LineReader(fromfile=fromfile,fromline=fromline).get_input_tree()
			if isinstance(tree,Stop):
				return False # stop running
			self.print_buffer += self.evaluate_tree(tree, env)
			self.flush()
		except AntlrException as e:
			print("\t!! antlr exception:",e.msg,"\t-- ignoring input")
		except RASPTypeError as e:
			print("\t!!statement executed, but result fails on evaluation:\n\t\t",e)
		except EOFError:
			#print() # newline
			return False # stop running
		except KeyboardInterrupt:
			print() # newline
		except Exception as e:
			if debug:
				raise e
			print("something went wrong:",e)
		return True # continue running

	def assigned_to_top(self,res,env):
		# only namedvals get set to begin with
		# self.env is toplevel
		# _* and out are private -> not toplevel
		if not isinstance(res,NamedVal):
			return True
		elif env is self.env:
			return True
		elif res.name.startswith("_"):
			return False
		elif res.name == "out":
			return False
		else:
			return True

	def evaluate_tree(self,tree,env):
		# (e.g. when loading from a file, make env for that file,
		# to keep that file's private (i.e. underscore-prefixed) variables to itself)
		try:
			if None is tree:
				return []
			elif tree.replstatement():
				return [self.evaluate_replstatement(tree.replstatement())]
			elif tree.raspstatement():
				res = Evaluator(env,self).evaluate(tree.raspstatement())
				return [r for r in res if self.assigned_to_top(r,env)]
			else: # if not replstatement or raspstatement, then comment
				return []
		except (UndefinedVariable, ReservedName) as e:
			return ["\t\t!!ignoring input:\n\t "+str(e)]
		except NotImplementedError:
			return ["not implemented this command yet! ignoring"]
		except (ArgsError,RASPTypeError,LoadError,RASPValueError) as e:
			return ["\t\t!!ignoring input:\n\t "+str(e)]

	def flush(self):
		#print(self.printing, self.print_buffer)
		if not self.printing:
			return
		# TODO: some error messages are still rising up and getting printed before reaching this position :(

		# rps is a list of NamedVals
		# go backwards - print last occurence of name per NamedVal, elminate other duplicate occurences
		names = set()
		for i,r in reversed(list(enumerate(self.print_buffer))):
			if isinstance(r,NamedVal):
				if r.name in names:
					self.print_buffer[i] = None
				names.add(r.name)
		# print list
		for r in self.print_buffer:
			self.print_result(r)
		self.print_buffer.clear()

	def run(self,fromfile=None,env=None):
		env = self.env if env is None else env
		running = True
		while running:
			running = self.run_tree(fromfile,None,env)
			self.flush()




from antlr4.error.ErrorListener import ErrorListener

class AntlrException(Exception):
	def __init__(self,msg):
		self.msg = msg

class InputNotFinished(Exception):
	def __init__(self):
		pass

class MyErrorListener( ErrorListener ):
	def __init__(self):
		super(MyErrorListener, self).__init__()

	def syntaxError(self, recognizer, offendingSymbol, line, column, msg, e):
		if offendingSymbol and offendingSymbol.text == "<EOF>":
			raise InputNotFinished()
		if msg.startswith("missing ';' at"):
			raise InputNotFinished()
		if "mismatched input" in msg:
			a=str(offendingSymbol)
			b=a[a.find("=")+2:]
			c=b[:b.find(",<")-1]
		ae = AntlrException(msg)
		ae.recognizer, ae.offendingSymbol, ae.line, ae.column, ae.msg, ae.e = recognizer, offendingSymbol, line, column, msg, e
		raise ae

	# def reportAmbiguity(self, recognizer, dfa, startIndex, stopIndex, exact, ambigAlts, configs):
		# raise AntlrException("ambiguity")

	# def reportAttemptingFullContext(self, recognizer, dfa, startIndex, stopIndex, conflictingAlts, configs):
		# we're ok with this: happens with func defs it seems

	# def reportContextSensitivity(self, recognizer, dfa, startIndex, stopIndex, prediction, configs):
		# we're ok with this: happens with func defs it seems

class Stop:
	def __init__(self):
		pass

class LineReader:
	__slots__ = ["fromfile","fromline","prompt","cont_prompt"]
	def __init__(self,prompt=">>",fromfile=None,fromline=None):
		self.fromfile = fromfile
		self.fromline = fromline
		self.prompt = prompt + " "
		self.cont_prompt = "."*len(prompt)+" "

	def str_to_antlr_parser(self,s):
		antlrinput = InputStream(s)
		lexer = RASPLexer(antlrinput)
		lexer.removeErrorListeners()
		lexer.addErrorListener( MyErrorListener() )
		stream = CommonTokenStream(lexer)
		parser = RASPParser(stream)
		parser.removeErrorListeners()
		parser.addErrorListener( MyErrorListener() )
		return parser

	def read_line(self,continuing=False,nest_depth=0):
		prompt = self.cont_prompt if continuing else self.prompt
		if not None is self.fromfile:
			res = self.fromfile.readline()
			return Stop() if not res else res # python files return "" on last line (as opposed to "\n" on empty lines)
		if not None is self.fromline:
			res = self.fromline
			self.fromline = Stop()
			return res
		else:
			return input(prompt+("  "*nest_depth))

	def get_input_tree(self):
		pythoninput = ""
		multiline = False
		while True:
			newinput = self.read_line(continuing=multiline,
			                          nest_depth=pythoninput.split().count("def"))
			if isinstance(newinput,Stop): # input stream ended
				return Stop()
			if is_comment(newinput):
				newinput = "" # don't let comments get in and ruin things somehow
			pythoninput += newinput # don't replace newlines! this is how in-function comments get broken .replace("\n","")+" "
			parser = self.str_to_antlr_parser(pythoninput)
			try:
				res = parser.r().statement()
				if isinstance(res,list):
					# TODO: this seems to happen when there's ambiguity. figure out what is going on!!
					assert len(res)==1
					res = res[0]
				return res
			except InputNotFinished:
				multiline = True
				pythoninput+=" "


def print_seq(example,seq,still_on_prev_line=False,extra_pref="",lastpref_if_shortprint=""):
	if len(set(seq.get_vals()))==1:
		print(extra_pref if not still_on_prev_line else "",
				lastpref_if_shortprint,
				str(seq),end=" ")
		print("[skipped full display: identical values]")# when there is only one value, it's nicer to just print that than the full list, verbosity be damned
		return
	if still_on_prev_line:
		print("")

	seq = seq.get_vals()
	def cleanboolslist(seq):
		if isinstance(seq[0],bool):
			tstr = "T" if seq.count(True) <= seq.count(False) else ""
			fstr = "F" if seq.count(False) <= seq.count(True) else ""
			return [tstr if v else fstr for v in seq]
		else:
			return seq

	example = cleanboolslist(example)
	seqtype = lazy_type_check(seq)
	seq = cleanboolslist(seq)
	example = [str(v) for v in example]
	seq = [str(v) for v in seq]
	maxlen = max(len(v) for v in example+seq)

	def neatline(seq):
		def padded(s):
			return " "*(maxlen-len(s))+s
		return " ".join(padded(v) for v in seq)

	print(extra_pref,"\t\tinput:  ",neatline(example),"\t","("+lazy_type_check(example)+"s)")
	print(extra_pref,"\t\toutput: ",neatline(seq),"\t","("+seqtype+"s)")

def print_select(example,select,extra_pref=""):
	# .replace("\n","\n\t\t\t")
	def nice_matrix_line(m):
		return " ".join("1" if v else " " for v in m)
	print(extra_pref,"\t\t\t    "," ".join(str(v) for v in example))
	matrix = select.get_vals()
	for v,m in zip(example,matrix):
		print(extra_pref,"\t\t\t",v,"|",nice_matrix_line(matrix[m]))

if __name__ == "__main__":
	myrepl = REPL().run()

# to run RASP from python
def runner():
	myrepl = REPL()
	try:
		myrepl.run()
	except Exception as e:
		print(e)
		return myrepl,e
	return myrepl,None
