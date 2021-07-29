from typing import Sized

from Sugar import select, zipmap, aggregate, \
				  tplor, tpland, tplnot, toseq, \
				  or_selects, and_selects, not_select, full_s, indices, length
from FunctionalSupport import Unfinished, UnfinishedSequence, UnfinishedSelect
from Support import RASPTypeError, RASPError
from collections.abc import Iterable
from zzantlr.RASPParser import RASPParser

encoder_name = "s-op"

def strdesc(o,desc_cap=None):
	if isinstance(o,Unfinished):
		return o.get_name()
	elif isinstance(o,list):
		res = "["+", ".join([strdesc(v) for v in o])+"]"
		if not None is desc_cap and len(res)>desc_cap:
			return "(list)"
		else:
			return res
	elif isinstance(o,dict):
		res = "{"+", ".join((strdesc(k)+": "+strdesc(o[k])) for k in o)+"}"
		if not None is desc_cap and len(res)>desc_cap:
			return "(dict)"
		else:
			return res
	elif isinstance(o,str):
		return "\""+o+"\""
	else:
		return str(o)


class RASPValueError(RASPError):
	def __init__(self,*a):
		super().__init__(*a)


debug = False
def debprint(*a,**kw):
	if debug:
		print(*a,**kw)

def ast_text(ast): # just so don't have to go remembering this somewhere
	# consider seeing if can make it add spaces between the tokens when doing this tho
	return ast.getText()

def isatom(v):
	# the legal atoms
	return True in [isinstance(v,t) for t in [int,float,str,bool]]

def name_general_type(v):
	if isinstance(v,list):
		return "list"
	if isinstance(v,dict):
		return "dict"
	if isinstance(v,UnfinishedSequence):
		return encoder_name
	if isinstance(v,UnfinishedSelect):
		return "selector"
	if isinstance(v,RASPFunction):
		return "function"
	if isatom(v):
		return "atom"
	return "??"

class ArgsError(Exception):
	def __init__(self,name,expected,got):
		super().__init__("wrong number of args for "+name+\
						"- expected: "+str(expected)+", got: "+str(got)+".")


class NamedVal:
	def __init__(self,name:str,val):
		self.name = name
		self.val = val
	def __str__(self):
		return f"NamedVal({self.name},{self.val})"

class RASPFunction:
	def __init__(self,name,enclosing_env,argnames,statement_trees,returnexpr,creator_name):
		self.name = name # just for debug purposes
		self.enclosing_env = enclosing_env
		self.argnames = argnames
		self.statement_trees = statement_trees
		self.returnexpr = returnexpr
		self.creator = creator_name

	def __str__(self):
		return self.creator + " function: "+self.name+"("+", ".join(self.argnames)+")"

	def __call__(self,*args) -> NamedVal:
		top_eval = args[-1]
		args = args[:-1]
		env = self.enclosing_env.make_nested([]) # nesting, because function shouldn't affect the enclosing environment
		if not len(args)==len(self.argnames):
			raise ArgsError(self.name,len(self.argnames),len(args))
		for n,v in zip(self.argnames,args):
			env.set_variable(n,v)
		evaluator = Evaluator(env,top_eval.repl)
		for at in self.statement_trees:
			evaluator.evaluate(at)
		res = evaluator.evaluateExprsList(self.returnexpr)
		return res[0] if len(res)==1 else NamedVal("out", [i.val for i in res])

class Evaluator:
	def __init__(self,env,repl):
		self.env = env
		self.sequence_running_example = repl.sequence_running_example
		self.repl = repl

	def evaluate(self,ast) -> list[NamedVal]:
		if ast.expr():
			return [self.evaluateExpr(ast.expr())]
		elif ast.assign():
			return self.assign(ast.assign())
		elif ast.funcDef():
			return [self.funcDef(ast.funcDef())]
		elif ast.draw():
			return [self.draw(ast.draw())]
		elif ast.forLoop():
			self.forLoop(ast.forLoop())
			return []
		elif ast.loadFile():
			self.repl.loadFile(ast.loadFile(),self.env)
			return []
		else:
			raise NotImplementedError

	def draw(self,ast) -> NamedVal:
	# TODO: make at least some rudimentary comparisons of selectors somehow to merge heads idk??????
	# maybe keep trace of operations used to create them and those with exact same parent s-ops and operations
	# can get in? would still find eg select(0,0,==) and select(1,1,==) different, but its better than nothing at all
		unf = self.evaluateExpr(ast.unf).val
		if not isinstance(unf.val,UnfinishedSequence):
			raise RASPTypeError("draw expects unfinished sequence, got:",unf)
		example = self.evaluateExpr(ast.inputseq).val if ast.inputseq else self.sequence_running_example
		if not isinstance(example.val,str):
			raise RASPTypeError("draw expects to evaluate sequence on string, got:",example)
		import DrawCompFlow; DrawCompFlow.draw_comp_flow(unf,example)
		res = unf(example)
		res.created_from_input = example
		return res

	def assign(self,ast) -> list[NamedVal]:
		def set_val_and_name(val,name):
			self.env.set_variable(name,val)
			if isinstance(val,Unfinished):
				val.setname(name) # completely irrelevant really for the REPL, 
				# but will help maintain sanity when printing computation flows
			return NamedVal(name,val)

		varnames = self._names_list(ast.var)
		values = self.evaluateExprsList(ast.val)
		if len(varnames) == len(values):
			return [set_val_and_name(val.val,name) for val,name in zip(values,varnames)]
		elif len(values) == 1 and isinstance(values[0].val,Sized) and len(varnames) == len(values[0].val):
			return [set_val_and_name(val,name) for val,name in zip(values[0].val,varnames)]
		else:
			raise RASPTypeError("expected",len(varnames),"values, but got:",len(values))

	def _names_list(self,ast):
		idsList = self._get_first_cont_list(ast)
		return [i.text for i in idsList]

	def _set_iterator_and_vals(self,iterator_names,iterator_vals):
		if len(iterator_names)==1:
			self.env.set_variable(iterator_names[0],iterator_vals)
		elif isinstance(iterator_vals,(Iterable,Sized)) and (len(iterator_vals)==len(iterator_names)):
			for n,v in zip(iterator_names,iterator_vals):
				self.env.set_variable(n,v)
		else:
			if not isinstance(iterator_vals,(Iterable,Sized)):
				raise RASPTypeError("iterating with multiple iterator names, but got single iterator value:",iterator_vals)
			else:
				assert not (len(iterator_vals)==len(iterator_names)), "something wrong with Evaluator logic" # should work out by logic of last failed elif
				raise RASPTypeError("iterating with",len(iterator_names),"names but got",len(iterator_vals),"values (",iterator_vals,")")

	def _evaluateDictComp(self,ast):
		ast = ast.dictcomp
		d = self.evaluateExpr(ast.iterable).val
		if not (isinstance(d,list) or isinstance(d,dict)):
			raise RASPTypeError("dict comprehension should have got a list or dict to loop over, but got:",l)
		res = {}
		iterator_names = self._names_list(ast.iterator) 
		for vals in d:
			orig_env = self.env
			self.env = self.env.make_nested()
			self._set_iterator_and_vals(iterator_names,vals)
			key = self.make_dict_key(ast.key)
			res[key] = self.evaluateExpr(ast.val).val
			self.env = orig_env
		return res


	def _evaluateListComp(self,ast):
		ast = ast.listcomp
		l = self.evaluateExpr(ast.iterable).val
		if not isinstance(l,(list,dict)):
			raise RASPTypeError("list comprehension should have got a list or dict to loop over, but got:",l)
		res = []
		iterator_names = self._names_list(ast.iterator) 
		for vals in l:
			orig_env = self.env
			self.env = self.env.make_nested()
			self._set_iterator_and_vals(iterator_names,vals) # sets inside the now-nested env - 
			# don't want to keep the internal iterators after finishing this list comp
			res.append(self.evaluateExpr(ast.val).val)
			self.env = orig_env
		return res

	def forLoop(self,ast):
		iterator_names = self._names_list(ast.iterator)
		iterable = self.evaluateExpr(ast.iterable).val
		if not (isinstance(iterable,list) or isinstance(iterable,dict)):
			raise RASPTypeError("for loop needs to iterate over a list or dict, but got:",iterable)
		statements = self._get_first_cont_list(ast.mainbody)
		for vals in iterable:
			self._set_iterator_and_vals(iterator_names,vals)
			for s in statements:
				self.evaluate(s)
		return


	def _get_first_cont_list(self,ast):
		res = []
		while ast:
			if ast.first:
				res.append(ast.first)
				# sometimes there's no first cause it's just eating a comment
			ast = ast.cont			
		return res

	def funcDef(self,ast) -> NamedVal:
		funcname = ast.name.text
		argname_trees = self._get_first_cont_list(ast.arguments)
		argnames = [a.text for a in argname_trees]
		statement_trees = self._get_first_cont_list(ast.mainbody)
		returnexpr = ast.retstatement.res
		res = RASPFunction(funcname,self.env,argnames,statement_trees,returnexpr,self.env.name)
		self.env.set_variable(funcname,res)
		return NamedVal(funcname,res)

	def _evaluateUnaryExpr(self,ast):
		uexpr = self.evaluateExpr(ast.uexpr).val
		uop = ast.uop.text
		if uop =="not":
			if isinstance(uexpr,UnfinishedSequence):
				return tplnot(uexpr)
			elif isinstance(uexpr,UnfinishedSelect):
				return not_select(uexpr)
			else:
				return not uexpr
		if uop =="-":
			return -uexpr
		if uop == "+":
			return +uexpr
		if uop =="round":
			return round(uexpr)
		if uop == "indicator":
			if isinstance(uexpr,UnfinishedSequence):
				name = "I("+uexpr.get_name()+")"
				return zipmap(uexpr,lambda a:1 if a else 0,name=name).allow_suppressing_display()
				# naming res makes RASP think it is important, i.e., 
				# must always be displayed. but here it has only been named for clarity, so 
				# correct RASP using .allow_suppressing_display()

			raise RASPTypeError("indicator operator expects "+encoder_name+", got:",uexpr)
		raise NotImplementedError

	def _evaluateRange(self,ast):
		valsList = [nval.val for nval in self.evaluateExprsList(ast.rangevals)]
		if not len(valsList) in [1,2,3]:
			raise RASPTypeError("wrong number of inputs to range, expected: 1, 2, or 3, got:",len(valsList))
		for v in valsList:
			if not isinstance(v,int):
				raise RASPTypeError("range expects all integer inputs, but got:",strdesc(valsList))
		return list(range(*valsList))

	def _index_into_dict(self,d,index):
		if not isatom(index):
			raise RASPTypeError("index into dict has to be atom (i.e., string, int, float, bool), got:",strdesc(index))
		if index not in d:
			raise RASPValueError("index [",strdesc(index),"] not in dict.")
		else:
			return d[index]

	def _index_into_list_or_str(self,l,index):
		lname = "list" if isinstance(l,list) else "string"
		if not isinstance(index,int):
			raise RASPTypeError("index into",lname,"has to be integer, got:",strdesc(index))
		if index>=len(l) or (-index)>len(l):
			raise RASPValueError("index",index,"out of range for",lname,"of length",len(l))
		return l[index]

	def _index_into_sequence(self,s,index):
		if isinstance(index,int):
			if index>=0:
				sel = select(toseq(index),indices,lambda q,k:q==k,name="load from "+str(index))
			else:
				real_index = length + index
				real_index.setname(length.name+str(index))
				sel = select(real_index,indices,lambda q,k:q==k,name="load from "+str(index))
			return aggregate(sel,s,name=s.name+"["+str(index)+"]").allow_suppressing_display()
		else:
			raise RASPValueError("index into sequence has to be integer, got:",strdesc(index))

		


	def _evaluateIndexing(self,ast):
		indexable = self.evaluateExpr(ast.indexable).val
		index = self.evaluateExpr(ast.index).val
		
		if isinstance(indexable,list) or isinstance(indexable,str):
			return self._index_into_list_or_str(indexable,index)
		elif isinstance(indexable,dict):
			return self._index_into_dict(indexable,index)
		elif isinstance(indexable,UnfinishedSequence):
			return self._index_into_sequence(indexable,index)
		else:
			raise RASPTypeError("can only index into a list, dict, string, or sequence, "+\
								 "but instead got:",strdesc(indexable))

	def _evaluateSelectExpr(self,ast):
		key = self.evaluateExpr(ast.key).val
		query = self.evaluateExpr(ast.query).val
		sop = ast.selop.text
		key = toseq(key) # in case got an atom in one of these, 
		query = toseq(query) # e.g. selecting 0th index: indices @= 0
		if sop=="<":
			return select(query,key,lambda q,k:q>k)
		if sop==">":
			return select(query,key,lambda q,k:q<k)
		if sop=="==":
			return select(query,key,lambda q,k:q==k)
		if sop=="!=":
			return select(query,key,lambda q,k:not (q==k))
		if sop=="<=":
			return select(query,key,lambda q,k:q>=k)
		if sop==">=":
			return select(query,key,lambda q,k:q<=k)

	def _evaluateBinaryExpr(self,ast):
		def either_sequence(l,r):
			return isinstance(l,UnfinishedSequence) or isinstance(r,UnfinishedSequence)
		def either_selector(l,r):
			return isinstance(l,UnfinishedSelect) or isinstance(r,UnfinishedSelect)
		def both_selector(l,r):
			return isinstance(l,UnfinishedSelect) and isinstance(r,UnfinishedSelect)
		left = self.evaluateExpr(ast.left).val
		right = self.evaluateExpr(ast.right).val
		bop = ast.bop.text
		bad_pair = RASPTypeError("Cannot apply and/or between selector and non-selector")
		if bop=="and":
			if either_sequence(left,right):
				if either_selector(left,right):
					raise bad_pair
				return tpland(left,right)
			elif either_selector(left,right):
				if not both_selector(left,right):
					raise bad_pair
				return and_selects(left,right)
			else:
				return (left and right)
		elif bop=="or":
			if either_sequence(left,right):
				if either_selector(left,right):
					raise bad_pair
				return tplor(left,right)
			elif either_selector(left,right):
				if not both_selector(left,right):
					raise bad_pair
				return or_selects(left,right)
			else:
				return (left or right)
		if either_selector(left,right):
			raise RASPTypeError("Cannot apply",bop,"to selector(s)")
		elif bop == "+":
			return left + right
		elif bop == "-":
			return left - right
		elif bop == "*":
			return left * right
		elif bop == "/":
			return left/right
		elif bop=="^":
			return pow(left,right)
		elif bop=='%':
			return left%right
		elif bop=="==":
			return left==right
		elif bop=="<=":
			return left<=right
		elif bop==">=":
			return left>=right
		elif bop=="<":
			return left<right
		elif bop==">":
			return left>right
		# more, like modulo and power and all the other operators, to come
		raise NotImplementedError

	def _evaluateStandalone(self,ast):
		if ast.anint:
			return int(ast.anint.text)
		if ast.afloat:
			return float(ast.afloat.text)
		if ast.astring:
			return ast.astring.text[1:-1]
		raise NotImplementedError

	def _evaluateTernaryExpr(self,ast):
		cond = self.evaluateExpr(ast.cond).val
		if isinstance(cond,Unfinished):
			res1 = self.evaluateExpr(ast.res1).val
			res2 = self.evaluateExpr(ast.res2).val
			cond, res1, res2 = tuple(map(toseq,(cond,res1,res2)))
			return zipmap((cond,res1,res2),
			    lambda c,r1,r2: r1 if c else r2,
			    name=res1.get_name()+" if "+cond.get_name()+" else "+res2.get_name()
			).allow_suppressing_display()
		else:
			return self.evaluateExpr(ast.res1).val if cond else self.evaluateExpr(ast.res2).val
			# lazy eval when cond is non-unfinished allows legal loops over actual atoms

	def _evaluateAggregateExpr(self,ast):
		sel = self.evaluateExpr(ast.sel).val
		seq = self.evaluateExpr(ast.seq).val
		seq = toseq(seq) # just in case its an atom
		default = self.evaluateExpr(ast.default).val if ast.default else None

		if not isinstance(sel,UnfinishedSelect):
			raise RASPTypeError("Expected selector, got:",strdesc(selector))
		if not isinstance(seq,UnfinishedSequence):
			raise RASPTypeError("Expected sequence, got:",strdesc(seq))
		if isinstance(default,Unfinished):
			raise RASPTypeError("Expected atom, got:",strdesc(default))
		return aggregate(sel,seq,default=default)



	def _evaluateZip(self,ast):
		list_exps = self._get_first_cont_list(ast.lists)
		lists = [self.evaluateExpr(e).val for e in list_exps]
		if not lists:
			raise RASPTypeError("zip needs at least one list")
		for i,l in enumerate(lists):
			if not isinstance(l,list):
				raise RASPTypeError("attempting to zip lists, but",i+1,"-th element is not list:",strdesc(l))
		n = len(lists[0])
		for i,l in enumerate(lists):
			if not len(l)==n:
				raise RASPTypeError("attempting to zip lists of length",n,", but",i+1,"-th list has length",len(l))
		return [list(v) for v in zip(*lists)] # keep everything lists, no tuples/lists mixing here, all the same to rasp (no stuff like append etc)

	def make_dict_key(self,ast):
		res = self.evaluateExpr(ast).val
		if not isatom(res):
			raise RASPTypeError("dictionary keys can only be atoms, but instead got:",strdesc(res))
		return res

	def _evaluateDict(self,ast):
		named_exprs_list = self._get_first_cont_list(ast.dictContents)
		return {self.make_dict_key(e.key):self.evaluateExpr(e.val).val for e in named_exprs_list}

	def _evaluateList(self,ast):
		exprs_list = self._get_first_cont_list(ast.listContents)
		return [self.evaluateExpr(e).val for e in exprs_list]

	def _evaluateApplication(self,ast,unf:Unfinished):
		input_vals = self._get_first_cont_list(ast.inputexprs)
		if not len(input_vals) == 1:
			raise ArgsError("evaluate unfinished",1,len(input_vals))
		input_val = self.evaluateExpr(input_vals[0]).val
		# if not isinstance(unf,Unfinished): # impossible
		# 	raise RASPTypeError("Applying unfinished expects to apply",encoder_name,"or selector, got:",strdesc(sel))
		if not isinstance(input_val,Iterable):
			raise RASPTypeError("Applying unfinished expects iterable input, got:",strdesc(input_val))
		res = unf(input_val)
		res.created_from_input = input_val
		return res

	def _evaluateRASPFunction(self,ast,raspfun:RASPFunction) -> NamedVal:
		args_trees = self._get_first_cont_list(ast.inputexprs)
		args = tuple(self.evaluateExpr(t).val for t in args_trees) + (self,)
		res: NamedVal = raspfun(*args)
		if isinstance(res.val,Unfinished):
			res.val.setname(raspfun.name+"("+" , ".join(strdesc(a,desc_cap=20) for a in args[:-1])+")")
		return res


	def _evaluateContains(self,ast):
		contained = self.evaluateExpr(ast.contained).val
		container = self.evaluateExpr(ast.container).val
		container_name = \
			ast.container.var.text if ast.container.var else str(container)
		if isinstance(contained,UnfinishedSequence):
			if not isinstance(container,list):
				raise RASPTypeError("\"["+encoder_name+"] in X\" expects X to be "\
					"list of atoms, but got non-list:",strdesc(container))
			for v in container:
				if not isatom(v):
					raise RASPTypeError("\"["+encoder_name+"] in X\" expects X to be "\
						"list of atoms, but got list with values:",strdesc(container))
			return zipmap(contained,lambda c:c in container,
								name=contained.name+" in "+container_name).allow_suppressing_display()
		elif isatom(contained): # contained is now an atom
			if isinstance(container,list):
				return contained in container
			elif isinstance(container,UnfinishedSequence):
				indicator = zipmap(container,lambda v:int(v==contained))
				return aggregate(full_s,indicator)>0
			else: 
				raise RASPTypeError("\"[atom] in X\" expects X to be list or "+encoder_name+", but got:",strdesc(container))
		if isinstance(contained,UnfinishedSelect) or isinstance(contained,RASPFunction):
			obj_name = "select" if isinstance(contained,UnfinishedSelect) else "function"
			raise RASPTypeError("don't check if",obj_name,
				"is contained in list/dict: unless exact same instance,",
				"unable to check equivalence of",obj_name+"s")
		else:
			raise RASPTypeError("\"A in X\" expects A to be",encoder_name,"or atom, but got A:",strdesc(contained))

	def _evaluateLen(self,ast):
		singleList = self.evaluateExpr(ast.singleList).val
		if not isinstance(singleList,list) or isinstance(singleList,dict):
			raise RASPTypeError("attempting to compute length of non-list:",strdesc(singleList))
		return len(singleList)

	def evaluateExprsList(self,ast) -> list[NamedVal]:
		exprsList = self._get_first_cont_list(ast)
		return [self.evaluateExpr(v) for v in exprsList]

	def evaluateExpr(self,ast) -> NamedVal:
		#print(ast.getText())
		def mkNamedVal(val,name:str="out") -> NamedVal:
			assert not isinstance(val,NamedVal)
			ast.evaled_value = val
			self.env.set_out(val)
			return NamedVal(name, val)
		if ast.bracketed: # in parentheses - get out of them
			return self.evaluateExpr(ast.bracketed)
		if ast.var: # calling single variable
			return mkNamedVal(self.env.get_variable(ast.var.text),name=ast.var.text)
		if ast.standalone:
			return mkNamedVal(self._evaluateStandalone(ast.standalone))
		if ast.bop:
			return mkNamedVal(self._evaluateBinaryExpr(ast))
		if ast.uop:
			return mkNamedVal(self._evaluateUnaryExpr(ast))
		if ast.cond:
			return mkNamedVal(self._evaluateTernaryExpr(ast))
		if ast.aggregate:
			return mkNamedVal(self._evaluateAggregateExpr(ast.aggregate))
		if ast.unfORfun:
			unfORfun = self.evaluateExpr(ast.unfORfun).val
			if isinstance(unfORfun,Unfinished):
				return mkNamedVal(self._evaluateApplication(ast,unfORfun))
			elif isinstance(unfORfun,RASPFunction):
				return self._evaluateRASPFunction(ast,unfORfun)
		if ast.selop:
			return mkNamedVal(self._evaluateSelectExpr(ast))
		if ast.aList():
			return mkNamedVal(self._evaluateList(ast.aList()))
		if ast.aDict():
			return mkNamedVal(self._evaluateDict(ast.aDict()))
		if ast.indexable: # indexing into a list, dict, or s-op
			return mkNamedVal(self._evaluateIndexing(ast))
		if ast.rangevals:
			return mkNamedVal(self._evaluateRange(ast))
		if ast.listcomp:
			return mkNamedVal(self._evaluateListComp(ast))
		if ast.dictcomp:
			return mkNamedVal(self._evaluateDictComp(ast))
		if ast.container:
			return mkNamedVal(self._evaluateContains(ast))
		if ast.lists:
			return mkNamedVal(self._evaluateZip(ast))
		if ast.singleList:
			return mkNamedVal(self._evaluateLen(ast))
		raise NotImplementedError

		
		

# new ast getText function for expressions
def new_getText(self): # original getText function stored as self._getText
	if hasattr(self,"evaled_value") and isatom(self.evaled_value):
		return str(self.evaled_value)
	else:
		return self._getText()

RASPParser.ExprContext._getText = RASPParser.ExprContext.getText
RASPParser.ExprContext.getText = new_getText
