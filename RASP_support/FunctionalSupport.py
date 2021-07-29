from Support import aggregate as _aggregate
from Support import Sequence, RASPTypeError
from Support import select as _select 
from Support import zipmap as _zipmap
import traceback, sys # for readable exception handling
from collections.abc import Iterable

name_maxlen = 30
plain_unfinished_name = "unf"
plain_unfinished_select_name = "sel"
plain_unfinished_sequence_name = "s-op"
plain_indices = "indices"
plain_tokens = "tokens"

# unique ids for all Unfinished objects, numbered by order of creation. ends up very useful sometimes
class NextId:
	def __init__(self):
		self.i = 0
	def get_next(self):
		self.i += 1
		return self.i

unique_id_maker = NextId()
def creation_order_id():
	return unique_id_maker.get_next()

class AlreadyPrintedTheException:
	def __init__(self):
		self.b = False
	def __bool__(self):
		return self.b

global_printed = AlreadyPrintedTheException()

# various unfinished objects
class Unfinished:
	def __init__(self,parents_tuple,parents2self,name=plain_unfinished_name,is_toplevel_input=False,min_poss_depth=-1):
		self.parents_tuple = parents_tuple
		self.parents2self = parents2self
		self.last_w = None
		self.last_res = None
		self.is_toplevel_input = is_toplevel_input
		self.setname(name if not self.is_toplevel_input else "input")
		self.creation_order_id = creation_order_id()
		self.min_poss_depth = min_poss_depth
		self.name = None

	def get_name(self):
		if self.name is None or len(self.name) > name_maxlen:
			if isinstance(self,UnfinishedSequence):
				return plain_unfinished_sequence_name
			elif isinstance(self,UnfinishedSelect):
				return plain_unfinished_select_name
			elif isinstance(self,UnfinishedSequencesTuple):
				return "plain unfinished tuple"
			else:
				return plain_unfinished_name
		return self.name

	def last_val(self):	
		return self.last_res.get_vals()

	#def draw_comp_flow(self,*a,**kw):
	#	import DrawCompFlow
	#	DrawCompFlow.draw_comp_flow(self,*a,**kw)

	def setname(self,name,always_display_when_named=True):
		assert name is not None
		self.name = name
		self.always_display = always_display_when_named # if you set something's name, you probably want to see it
		return self # return self to allow chaining with other calls and throwing straight into a return statement etc

	def __call__(self,w,print_all_named_sequences=False,print_input=False,
					print_all_sequences=False,print_all=False,have_printed=global_printed,topcall=True):
		if (not isinstance(w,Iterable)) or (not w):
			raise RASPTypeError("RASP sequences/selectors expect non-empty iterables, got: "+str(w))
		global_printed.b = False
		if w == self.last_w:
			return self.last_res # don't print same calculation multiple times
		else:
			if self.is_toplevel_input:
				res = w
				self.last_w, self.last_res = w, w
			else:
				try:
					res = self.parents2self(*tuple(p(w,
												print_all_named_sequences=print_all_named_sequences,
												print_input=print_input,
												print_all_sequences=print_all_sequences,
												print_all=print_all,
												topcall=False) 
											for p in self.parents_tuple))
				except Exception as e:
					if isinstance(e,RASPTypeError):
						raise e
					if not global_printed.b:
						print("===============================================================")
						print("===============================================================")
						print("evaluation failed in: [",self.get_name(),"] with exception:\n",e)
						print("===============================================================")
						print("parent values are:")
						for p in self.parents_tuple:
							print("=============")
							print(p.get_name())
							print(p.last_res)
						print("===============================================================")
						print("===============================================================")
						a,b,tb = sys.exc_info()
						tt = traceback.extract_tb(tb)
						last_call = max([i for i,t in enumerate(tt) if "__call__" in str(t)])
						print(''.join(traceback.format_list(tt[last_call+1:])))

						# traceback.print_exception(a,b,tb)

					global_printed.b = True
					if not topcall:
						raise
					else:
						return "EVALUATION FAILURE"

				self.last_w, self.last_res = w, res

		def should_print():
			if isinstance(res,Sequence):
				if print_all_named_sequences and not (self.name in plain_names):
					return True
				if print_all_sequences:
					return True
				if self.is_toplevel_input and print_input:
					return True
			return print_all
		if should_print(): 
			print("resolved \""+self.name+\
				(("\" from:\" "+str(self.get_own_root_input(w))+" \"") if print_root_inputs_too else ""),\
				":\n\t",res)
		return res

class UnfinishedSequence(Unfinished):
	def __init__(self,parents_tuple,parents2self,name=plain_unfinished_sequence_name,
	elementwise_function=None,default=None,min_poss_depth=0,from_zipmap=False,
	output_index=-1,definitely_uses_identity_function=False):
	# min_poss_depth=0 starts all of the base sequences (eg indices) off right
		if None is name: # might have got none from some default value, fix it before continuing because later things eg DrawCompFlow
			name = plain_unfinished_sequence_name  # will expect name to be a string
		super(UnfinishedSequence, self).__init__(parents_tuple,parents2self,name=name,min_poss_depth=min_poss_depth)
		self.from_zipmap = from_zipmap # can be inferred (by seeing if there are parent selects), but this is simple enough. helpful for rendering comp flow visualisations
		self.elementwise_function = elementwise_function # useful for analysis later
		self.output_index = output_index
		self.default = default # useful for analysis later
		self.definitely_uses_identity_function = definitely_uses_identity_function
		self.never_display = False
		self._constant = False

	def __str__(self):
		return "UnfinishedSequence(name="+self.get_name()+",id="+str(self.creation_order_id)+")"
	def mark_as_constant(self):
		self._constant = True
		return self
	def is_constant(self):
		return self._constant


class UnfinishedSelect(Unfinished):
	def __init__(self,parents_tuple,parents2self,
					name=plain_unfinished_select_name,compare_string=None,min_poss_depth=-1,
					q_vars=None,k_vars=None,orig_selector=None): # selects should be told their depth, -1 will warn of problems properly
		if None is name: # as in unfinishedsequence, some other function might have passed in a None somewhere
			name = plain_unfinished_select_name # so fix before a print goes wrong
		super(UnfinishedSelect, self).__init__(parents_tuple,parents2self,name=name,min_poss_depth=min_poss_depth)
		self.compare_string = str(self.creation_order_id) if None is compare_string else compare_string
		assert not None in [q_vars,k_vars] # they're not really optional i just dont want to add more mess to the func
		self.q_vars = q_vars # don't actually need them, but useful for
		self.k_vars = k_vars # drawing comp flow
		# use compare string for comparison/uniqueness rather than overloading __eq__ of unfinishedselect,
		# to avoid breaking things in unknown locations, and to be able to put selects in dictionaries 
		# and stuff (overloading __eq__ makes an object unhasheable unless i guess you overload the 
		# hash too?). need these comparisons for optimisations in analysis eg if two selects are identical 
		# they can be same head
		self.orig_selector = orig_selector # for comfortable compositions of selectors
	def __str__(self):
		return "UnfinishedSelect(name="+self.name+",id="+str(self.creation_order_id)+")"


# some tiny bit of sugar that fits here:
def is_sequence_of_unfinishedseqs(seqs):
	if not isinstance(seqs,Iterable):
		return False
	return False not in [isinstance(seq,UnfinishedSequence) for seq in seqs]

class BareBonesFunctionalSupportException(Exception):
	def __init__(self,m):
		Exception.__init__(self,m)

def to_tuple_of_unfinishedseqs(seqs):
	if is_sequence_of_unfinishedseqs(seqs):
		return tuple(seqs)
	if isinstance(seqs,UnfinishedSequence):
		return (seqs,)
	print("seqs:",seqs)
	raise BareBonesFunctionalSupportException(
			"input to select/aggregate not an unfinished sequence or sequence of unfinished sequences")

tup2tup = lambda *x:tuple([*x])
class UnfinishedSequencesTuple(Unfinished):
	def __init__(self,parents_tuple,parents2self=None):
		# sequence tuples only exist in here, user doesn't 'see' them. can have lots of default values 
		# they're just a convenience for me
		if None is parents2self: # just sticking a bunch of unfinished sequences together into one thing for reasons
			parents2self = tup2tup
			parents_tuple = to_tuple_of_unfinishedseqs(parents_tuple)
			assert is_sequence_of_unfinishedseqs(parents_tuple) and isinstance(parents_tuple,tuple)
		# else - probably creating several sequences at once from one aggregate
		super(UnfinishedSequencesTuple, self).__init__(parents_tuple,parents2self)
	def __add__(self,other):
		assert isinstance(other,UnfinishedSequencesTuple)
		assert self.parents2self is tup2tup
		assert other.parents2self is tup2tup
		return UnfinishedSequencesTuple(self.parents_tuple+other.parents_tuple)


_input = Unfinished((),None,is_toplevel_input=True)
#### and now, the actual exposed functions
indices = UnfinishedSequence((_input,),lambda w:Sequence(list(range(len(w)))),name=plain_indices)
tokens_str = UnfinishedSequence((_input,),lambda w:Sequence(list(map(str,w))),name=plain_tokens+"_str")
tokens_int = UnfinishedSequence((_input,),lambda w:Sequence(list(map(int,w))),name=plain_tokens+"_int")
tokens_float = UnfinishedSequence((_input,),lambda w:Sequence(list(map(float,w))),name=plain_tokens+"_float")
tokens_bool = UnfinishedSequence((_input,),lambda w:Sequence(list(map(bool,w))),name=plain_tokens+"_bool")
tokens_asis = UnfinishedSequence((_input,),lambda w:Sequence(w),name=plain_tokens+"_asis")
base_tokens = [tokens_str,tokens_int,tokens_float,tokens_bool,tokens_asis]

def _min_poss_depth(unfs):
	if isinstance(unfs,Unfinished): # got single unfinished and not iterable of them
		unfs = [unfs]
	return max([u.min_poss_depth for u in unfs]+[0]) # max b/c cant go less deep than deepest
	# add that 0 thing so list is never empty and max complains.

def tupleise(v):
	if isinstance(v,tuple) or isinstance(v,list):
		return tuple(v)
	return (v,)

def select(q_vars,k_vars,selector,name=None,compare_string=None):
	if None is name:
		name = "plain select"
	# potentially here check the qvars all reference the same input sequence as each other and same for the kvars,
	# technically dont *have* to but is helpful for the user so consider maybe adding a tiny bit of mess here 
	# (including markings inside sequences and selectors so they know which index they're gathering to and from) 
	# to allow it
	q_vars = tupleise(q_vars) # we're ok with getting a single q or k var, not in a tuple,
	k_vars = tupleise(k_vars) # but important to fix it before '+' on two UnfinishedSequences 
	# (as opposed to two tuples) sends everything sideways
	new_depth = _min_poss_depth(q_vars+k_vars)+1 # attn layer is one after values it needs to be calculated
	res = UnfinishedSelect((_input, # need input seq length to create select of correct size
							 UnfinishedSequencesTuple(q_vars),
							 UnfinishedSequencesTuple(k_vars)  ), 
							 lambda input_seq,qv,kv: _select(len(input_seq),qv,kv,selector),
								 name=name,compare_string=compare_string,min_poss_depth=new_depth,
								 q_vars=q_vars,k_vars=k_vars,orig_selector=selector)
	return res

def _compose_selects(select1,select2,compose_op=None,name=None,compare_string=None):
	nq1 = len(select1.q_vars)
	nq2 = len(select2.q_vars)+nq1
	nk1 = len(select1.k_vars)+nq2

	def new_selector(*qqkk):
		q1 = qqkk[:nq1]
		q2 = qqkk[nq1:nq2]
		k1 = qqkk[nq2:nk1]
		k2 = qqkk[nk1:]
		return compose_op(select1.orig_selector(*q1,*k1), select2.orig_selector(*q2,*k2))
	return select(select1.q_vars+select2.q_vars,
				  select1.k_vars+select2.k_vars,
				  new_selector,name=name,compare_string=compare_string)

def _compose_select(select1,compose_op=None,name=None,compare_string=None):
	def new_selector(*qk):
		return compose_op(select1.orig_selector(*qk))
	return select(select1.q_vars,
				  select1.k_vars,
				  new_selector,name=name,compare_string=compare_string)

def not_select(select,name=None,compare_string=None):
	return _compose_select(select,lambda a:not a,
					name=name,compare_string=compare_string)

def and_selects(select1,select2,name=None,compare_string=None):
	return _compose_selects(select1,select2,lambda a,b:a and b,
					name=name,compare_string=compare_string)

def or_selects(select1,select2,name=None,compare_string=None):
	return _compose_selects(select1,select2,lambda a,b:a or b,
					name=name,compare_string=compare_string)

def example_input():
	return [100] # all the input types (str, int, float, bool), should be able to convert 0 to their own type when go to evaluate tokens
	# when come to have multiple inputs, this wont fly, becuase will be expecting list of iterables. consider making optional argument
	# that says 'i have not broken it into a list of the different inputs, it is presented here with seperators'  which of course it cant
	# be because the seperators will be special classes to avoid trouble, but basically it will just interpret it as all sequences except 
	# the first being empty 

def format_output(example_output,parents_tuple,parents2res,name,elementwise_function=None,
						default=None,min_poss_depth=0,from_zipmap=False,
						definitely_uses_identity_function=False):
	if not isinstance(example_output,tuple):
		return UnfinishedSequence(parents_tuple,parents2res,
				elementwise_function=elementwise_function,default=default,
				name=name,min_poss_depth=min_poss_depth,from_zipmap=from_zipmap,
				definitely_uses_identity_function=definitely_uses_identity_function)
	else:
		num_outputs = len(example_output)
		names = name
		if not isinstance(names,list) or isinstance(names,tuple):
			names = [names]*num_outputs
		assert len(names) == num_outputs
		def get_ith_output(i):
			return lambda x:x[i] # would have this lambda directly below,
			# but python will have this horrible thing where it then takes 
			# the last value that the variable 'i' had for the lambda
		unfinished_results_tuple = UnfinishedSequencesTuple(parents_tuple,parents2res)
		return tuple( UnfinishedSequence((unfinished_results_tuple,),
										  get_ith_output(i), 
										  elementwise_function=elementwise_function,
										  default=default,
										  name=names[i],
										  min_poss_depth=min_poss_depth,
										  from_zipmap=from_zipmap,
										  output_index=i,
										  definitely_uses_identity_function=definitely_uses_identity_function) 
															for i in range(num_outputs))

def get_identity_function(num_params):
	def identity1(a):
		return a
	def identityx(*a):
		return a
	return identity1 if num_params==1 else identityx

def zipmap(sequences_tuple,elementwise_function,name=plain_unfinished_sequence_name):
	sequences_tuple = tupleise(sequences_tuple)
	unfinished_parents_tuple = UnfinishedSequencesTuple(sequences_tuple) # this also takes care of turning the 
	# value in sequences_tuple to indeed a tuple of sequences and not eg a single sequence which will 
	# cause weird behaviour later
	example_parents = unfinished_parents_tuple(example_input())
	example_output = _zipmap(len(example_input()),example_parents,elementwise_function)
	parents_tuple = (_input,unfinished_parents_tuple)
	parents2res = lambda w,vt: _zipmap(len(w),vt,elementwise_function)
	min_poss_depth = _min_poss_depth(sequences_tuple) # feedforward doesn't increase layer
	# new assumption, to be revised later: can do arbitrary zipmap even before first feed-forward,
	# i.e. in build up to first attention. truth is can do 'simple' zipmap towards first attention
	# (no xor, but yes things like 'and' or 'indicator for ==' or whatever) based on initial linear
	# translation done for Q,K in attention (not deep enough for xor, but deep enough for simple stuff)
	# alongside use of initial embedding. honestly literally can just put everything in initial embedding
	# if need it so bad its the first layer and its zipmap its only a function of the token and indices,
	# so long as its not computing any weird combination between them you can do it in the embedding
	# if len(sequences_tuple)>0: 
	# 	min_poss_depth = max(min_poss_depth,1) # except for the very specific case where
	# 	# it is the very first thing to be done, in which case we do have to go through 
	# 	# one layer to get to the first feedforward.
	# 	# the 'if' is there to rule out increasing when doing a feedforward on nothing,
	# 	# ie, when making a constant. constants are allowed to be created on layer 0, they're
	# 	# part of the embedding or the weights that will use them later or whatever, it's fine
	return format_output(example_output,parents_tuple,parents2res,name,
					min_poss_depth=min_poss_depth,elementwise_function=elementwise_function,
					from_zipmap=True) # at least as deep as needed MVs, but no 
					# deeper cause FF (which happens at end of layer)

def aggregate(select,sequences_tuple,elementwise_function=None,
				default=None,name=plain_unfinished_sequence_name): 
	sequences_tuple = tupleise(sequences_tuple)
	definitely_uses_identity_function = None is elementwise_function 
	if definitely_uses_identity_function:
		elementwise_function = get_identity_function(len(sequences_tuple))
	unfinished_parents_tuple = UnfinishedSequencesTuple(sequences_tuple)
	example_output = _aggregate(select(example_input()),
		unfinished_parents_tuple(example_input()),elementwise_function,default=default)
	parents_tuple = (select,unfinished_parents_tuple)
	parents2res = lambda s,vt:_aggregate(s,vt,elementwise_function,default=default)
	return format_output(example_output,parents_tuple,parents2res,name,
				elementwise_function=elementwise_function,default=default,
				min_poss_depth=max(_min_poss_depth(sequences_tuple)+1,select.min_poss_depth),
				definitely_uses_identity_function=definitely_uses_identity_function)
				# at least as deep as needed attention and at least one deeper than needed MVs

########### up to here was just plain transformer 'assembly'. any addition is a lie ##############
##################### now begin the bells and whistles ###########################################

def UnfinishedSequenceFunc(f):
	setattr(UnfinishedSequence,f.__name__,f)

def UnfinishedFunc(f):
	setattr(Unfinished,f.__name__,f)



@UnfinishedSequenceFunc
def allow_suppressing_display(self):
	self.always_display = False
	return self # return self to allow chaining with other calls and throwing straight into a return statement etc

# later, we will overload == for unfinished sequences, such that it always returns another 
# unfinished sequence. unfortunately this creates the following upsetting behaviour: 
# "a in l" and "a==b" always evaluates to true for any unfinishedsequences a,b and non-empty 
# list l, and any item a and list l containing at least one unfinished sequence. hence, to
# check if a sequence is really in a list we have to do it ourselves, some other way.

def guarded_compare(seq1,seq2):
	if isinstance(seq1,UnfinishedSequence) or isinstance(seq2,UnfinishedSequence):
		return seq1 is seq2
	return seq1 == seq2

def guarded_contains(l,a):
	if isinstance(a,Unfinished):
		return True in [(a is e) for e in l]
	else:
		l = [e for e in l if not isinstance(e,Unfinished)]
		return a in l
