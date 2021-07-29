from Sugar import tokens_asis, tokens_str, tokens_int, tokens_bool, tokens_float, indices, length
from FunctionalSupport import Unfinished, RASPTypeError
from Support import Sequence, Select
from Evaluator import RASPFunction
from copy import deepcopy

class UndefinedVariable(Exception):
	def __init__(self,varname):
		super().__init__("Error: Undefined variable: "+varname)

class ReservedName(Exception):
	def __init__(self,varname):
		super().__init__("Error: Cannot set reserved name: "+varname)

class Environment:
	def __init__(self,parent_env=None,name=None,stealing_env=None):
		self.variables = {}
		self.name = name
		self.parent_env = parent_env
		self.stealing_env = stealing_env
		self.base_setup() # nested envs can have them too. makes life simpler,
		# instead of checking if they have the constant_variables etc in get. bit heavier on memory
		# but no one's going to use this language for big nested stuff anyway

	def base_setup(self):
		self.constant_variables = {
			"tokens_asis":tokens_asis,
			"tokens_str":tokens_str,
			"tokens_int":tokens_int,
			"tokens_bool":tokens_bool,
			"tokens_float":tokens_float,
			"indices":indices,
			"length":length,
			"True":True,
			"False":False}
		self.reserved_words=["if","else","not","and","or","out","def","return","range","for","in","zip","len","get"] + \
										list(self.constant_variables.keys())

	def snapshot(self):
		res = Environment(parent_env=self.parent_env,name=self.name,stealing_env=self.stealing_env)
		def deepcopy(val):
			if isinstance(val,(Unfinished,RASPFunction,float,int,str,bool)):
				return val # non mutable (at least not through rasp commands)
			elif isinstance(val,list):
				return [deepcopy(v) for v in val]
			elif isinstance(val,dict): # TODO was this missing?
				return {k:deepcopy(v) for k,v in val.values()}
			else:
				raise RASPTypeError("environment contains element that is not unfinished,",
									"rasp function, float, int, string, bool, or list? :",val)
		res.variables = {d:deepcopy(self.variables[d]) for d in self.variables}
		return res

	def make_nested(self,names_vars=None):
		names_vars = [] if names_vars is None else names_vars
		res = Environment(self,name=str(self.name)+"'")
		for n,v in names_vars:
			res.set_variable(n,v)
		return res

	def get_variable(self,name):
		if name in self.constant_variables:
			return self.constant_variables[name]
		if name in self.variables:
			return self.variables[name]
		if not None is self.parent_env:
			return self.parent_env.get_variable(name)
		raise UndefinedVariable(name)

	def set_variable(self,name,val):
		assert isinstance(val,(Unfinished,RASPFunction,float,int,str,bool,list,dict)), val
		if name in self.reserved_words:
			raise ReservedName(name)
		self.variables[name] = val
		if not None is self.stealing_env:
			if name.startswith("_") or name=="out": # things we don't want to steal
				return
			self.stealing_env.set_variable(name,val)

	def set_out(self,val):
		assert isinstance(val,(Unfinished,RASPFunction,float,int,str,bool,list,dict,Sequence)), val
		self.variables["out"] = val
