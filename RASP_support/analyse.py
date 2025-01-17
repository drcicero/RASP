from FunctionalSupport import Unfinished, UnfinishedSequence, UnfinishedSelect, \
guarded_contains, guarded_compare, zipmap # need these for actually comparing sequences and not just making more sequences 
from collections import defaultdict, Counter
from copy import copy

def UnfinishedFunc(f):
	setattr(Unfinished,f.__name__,f)

def is_real_unfinished(unf): # as opposed to intermediate unfinisheds like tuples of sequences
	return isinstance(unf,UnfinishedSequence) or isinstance(unf,UnfinishedSelect)

Unfinished._parents = None
@UnfinishedFunc
def get_parents(self):
	if not None is self._parents:
		return self._parents
	real_parents_part1 = [p for p in self.parents_tuple if is_real_unfinished(p)]
	other_parents = [p for p in self.parents_tuple if not is_real_unfinished(p)]
	res = real_parents_part1
	for p in other_parents: 
		res += p.get_parents() # recursion: branch back through all the parents of the unf, 
		# always stopping wherever hit something 'real' ie a select or a sequence
	assert len([p for p in res if isinstance(p,UnfinishedSelect)]) <= 1 # nothing is made from more than one select...
	self._parents = list(set(res))
	return copy(self._parents) # in case someone messes with the list eg popping through it

@UnfinishedFunc
def get_parent_sequences(self):
	# for UnfinishedSequences, this should get just the tuple of sequences the aggregate is applied to,
	# and I think in order (as the parents will only be a select and a sequencestuple, and the seqs in the
	# sequencestuple will be added in order and the select will be removed in this function)
	return [p for p in self.get_parents() if isinstance(p,UnfinishedSequence)] # i.e. drop the selects

Unfinished._full_parents = None
@UnfinishedFunc
def get_full_parents(self):
	if None is self._full_parents:
		explored = set()
		not_explored = [self]
		while not_explored:
			p = not_explored.pop(0)
			new_parents = p.get_parents()
			explored.add(p)
			not_explored += [p for p in new_parents if not guarded_contains(explored,p)]
		self._full_parents = explored
	return copy(self._full_parents)

Unfinished._full_seq_parents = None
@UnfinishedFunc
def get_full_seq_parents(self):
	if None is self._full_seq_parents:
		self._full_seq_parents = [u for u in self.get_full_parents() \
									if isinstance(u,UnfinishedSequence)]
	return copy(self._full_seq_parents)

@UnfinishedFunc
def get_parent_select(self):
	if not hasattr(self,"parent_select"):		
		real_parents = self.get_parents()
		self.parent_select = next((s for s in real_parents if \
								isinstance(s,UnfinishedSelect)), None)
	return self.parent_select

@UnfinishedFunc
def set_analysis_parent_select(self,options): 
	# doesn't really need to be a function but feels clearer visually to have it
	# out here so i can see this variable is being registered to the unfinisheds
	if None is self.parent_select:
		self.analysis_parent_select = self.parent_select
	else:
		self.analysis_parent_select = next((ps for ps in options if \
						ps.compare_string==self.get_parent_select().compare_string), None)
		assert not None is self.analysis_parent_select, "parent options given to seq: "+self.name+" did not"+\
													"include anything equivalent to actual seq's parent"+\
													" select ("+self.get_parent_select().compare_string+")"

def squeeze_selects(selects):
	compstrs = set([s.compare_string for s in selects])
	if len(compstrs) == len(selects):
		return selects
	return [next(s for s in selects if s.compare_string==cs) for cs in compstrs]

@UnfinishedFunc
def schedule(self,scheduler='best',remove_minors=False): 
# recall attentions can be created on level 1 but still generate seqs on level 3 etc
# hence width is number of *seqs* with different attentions per level.
	def choose_scheduler(scheduler):
		if scheduler == 'best':
			return 'greedy' 
			# TODO: implement lastminute, maybe others, and choose narrowest 
			# result of all options
		return scheduler
	scheduler = choose_scheduler(scheduler)
	seq_layers = self.greedy_seq_scheduler() if scheduler == 'greedy' \
								else self.lastminute_seq_scheduler()

	if remove_minors:
		for i in seq_layers:
			seq_layers[i] = [seq for seq in seq_layers[i] if not seq.is_minor]

	num_layers = max(seq_layers.keys())

	def get_seqs_selects(seqs):
		# all the selects needed to compute a set of seqs
		all_selects = set(seq.get_parent_select() for seq in seqs)
		all_selects -= set([None]) # some of the seqs may not have parent matches, 
		# eg, indices. these will return None, which we don't want to count
		return squeeze_selects(all_selects) # squeeze identical parents


	layer_selects = { i:get_seqs_selects(seq_layers[i]) for i in seq_layers }

	# mark remaining parent select after squeeze
	for i in seq_layers:
		for seq in seq_layers[i]:
			seq.set_analysis_parent_select(layer_selects[i])

	return seq_layers, layer_selects

@UnfinishedFunc
def greedy_seq_scheduler(self):
	all_seqs = sorted(self.get_full_seq_parents(),
						key = lambda seq:seq.creation_order_id) 
	# sorting in order of creation automatically sorts by order of in-layer 
	# dependencies (i.e. things got through feedforwards), makes prints clearer 
	# and eventually is helpful for drawcompflow
	levels = defaultdict(lambda :[])
	for seq in all_seqs:
		levels[seq.min_poss_depth].append(seq) # schedule all seqs as early as possible
	return levels


Unfinished.max_poss_depth_for_seq = (None,None)
@UnfinishedFunc
def lastminute_for_seq(self,seq):
	raise NotImplementedError


@UnfinishedFunc
def lastminute_seq_scheduler(self):
	all_seqs = self.get_full_seq_parents()


@UnfinishedFunc
def typestr(self):
	if isinstance(self,UnfinishedSelect):
		return "select"
	elif isinstance(self,UnfinishedSequence):
		return "seq"
	else:
		return "internal"

@UnfinishedFunc
def width_and_depth(self,scheduler='greedy',loud=True,print_tree_too=False,remove_minors=False):
	seq_layers, layer_selects = self.schedule(scheduler=scheduler,remove_minors=remove_minors)
	widths = {i:len(layer_selects[i]) for i in layer_selects}
	n_layers = max(seq_layers.keys())
	max_width = max(widths[i] for i in widths)
	if loud:
		print("analysing unfinished",self.typestr()+":",self.name)
		print("using scheduler:",scheduler)
		print("num layers:",n_layers,"max width:",max_width)
		print("width per layer:")
		print("\n".join( str(i)+"\t: "+str(widths[i]) \
						for i in range(1,n_layers+1) )) 
						# start from 1 to skip layer 0, which has width 0 
						# and is just the inputs (tokens and indices)
		if print_tree_too:
			def print_layer(i,d):
				print(i,"\t:",", ".join(seq.name for seq in d[i]))
			print("==== seqs at each layer: ====")
			[print_layer(i,seq_layers) for i in range(1,n_layers+1)]
			print("==== selects at each layer: ====")
			[print_layer(i,layer_selects) for i in range(1,n_layers+1)]
	return n_layers, max_width, widths

@UnfinishedFunc
def schedule_comp_depth(self,d):
	self.scheduled_comp_depth = d

@UnfinishedFunc
def get_all_ancestor_heads_and_ffs(self,remove_minors=False):
	class Head:
		def __init__(self,select,sequences,comp_depth):
			self.comp_depth = comp_depth
			self.name = str([m.name for m in sequences])
			self.sequences = sequences
			self.select = select
	seq_layers, layer_selects = self.schedule('best',remove_minors=remove_minors)

	all_ffs = [m for m in self.get_full_seq_parents() if m.from_zipmap]
	if remove_minors:
		all_ffs = [ff for ff in all_ffs if not ff.is_minor]

					
	for i in seq_layers:
		for m in seq_layers[i]:
			if guarded_contains(all_ffs,m):
				m.schedule_comp_depth(i) # mark comp depths of the ffs... drawcompflow wants to know

	heads = []
	for i in layer_selects:
		for s in layer_selects[i]:
			seqs = [m for m in seq_layers[i] if m.analysis_parent_select==s]
			heads.append(Head(s,seqs,i))

	return heads,all_ffs

@UnfinishedFunc
def set_display_name(self,display_name):
	self.display_name = display_name
	# again just making it more visible??? that there's an attribute being set somewhere

@UnfinishedFunc
def make_display_names_for_all_parents(self,skip_minors=False):
	all_unfs = self.get_full_parents()
	all_seqs = [u for u in set(all_unfs) if isinstance(u,UnfinishedSequence)]
	all_selects = [u for u in set(all_unfs) if isinstance(u,UnfinishedSelect)]
	if skip_minors:
		num_orig = len(all_seqs)
		all_seqs = [seq for seq in all_seqs if not seq.is_minor]
	name_counts = Counter([m.name for m in all_seqs])
	name_suff = Counter()
	for m in sorted(all_seqs+all_selects,key=lambda u:u.creation_order_id): 
	# yes, even the non-seqs need display names, albeit for now only worry about repeats in the seqs
	# and sort by creation order to get name suffixes with chronological (and so non-confusing) order
		if name_counts[m.name]>1:
			m.set_display_name(m.name+"_"+str(name_suff[m.name]))
			name_suff[m.name] += 1

		else:
			m.set_display_name(m.name)

@UnfinishedFunc
def note_if_seeker(self):
	if not isinstance(self,UnfinishedSequence):
		return

	if (not self.get_parent_sequences()) and (not None is self.get_parent_select()): 
	# no parent sequences, but yes parent select: this value is a function 
	# of only its parent select, i.e., a seeker (marks whether select found something or not)
		self.is_seeker = True
		self.seeker_flag = self.elementwise_function()
		self.seeker_default = self._default
	else:
		self.is_seeker = False

@UnfinishedFunc
def mark_all_ancestor_seekers(self):
	[u.note_if_seeker() for u in self.get_full_parents()]

Unfinished._full_descendants_for_seq = (None,None)
@UnfinishedFunc
def descendants_towards_seq(self,seq):
	if not guarded_compare(self._full_descendants_for_seq[0],seq):
		
		relevant = seq.get_full_parents()
		res = [r for r in relevant if guarded_contains(r.get_parents(),self)]

		self._full_descendants_for_seq = (seq,res)
	return self._full_descendants_for_seq[1]
	
@UnfinishedFunc
def is_minor_comp_towards_seq(self,seq):
	if not isinstance(self,UnfinishedSequence):
		return False # selects are always important
	if self.never_display: # priority: never over always
		return True
	if self.always_display:
		if self.is_constant():
			print("displaying constant:",self.name)
		return False 
	if self.is_constant(): # e.g. 1 or "a" etc, just stuff created around constants by REPL behind the scenes
		return True
	children = self.descendants_towards_seq(seq)
	if len(children)>1:
		return False # this sequence was used twice -> must have been actually 
		# named as a real variable in the code (and not part of some bunch of operators)
		# -> make it visible in the comp flow too
	if len(children)==0:
		return not guarded_compare(self,seq) # if it's the seq itself then clearly 
		# we're very interested in it. if it has no children and isnt the seq then we're checking out 
		# a weird dangly unused leaf, we shouldn't reach such a scenario through any of functions 
		# we'll be using to call this one, but might as well make this function complete just in case
		# we forget
	child = children[0]
	if isinstance(child,UnfinishedSelect):
		return False # this thing feeds directly into a select, lets make it visible
	return (child.from_zipmap and self.from_zipmap) # obtained through zipmap and feeds
	# directly into another zipmap: minor operation as part of something more complicated

Unfinished.is_minor = False
@UnfinishedFunc
def set_minor_for_seq(self,seq): # another func just to be very explicit about an attribute that's getting set
	self.is_minor = self.is_minor_comp_towards_seq(seq)
	
@UnfinishedFunc
def mark_all_minor_ancestors(self):
	all_ancestors = self.get_full_parents()
	for a in all_ancestors:
		a.set_minor_for_seq(self)

@UnfinishedFunc
def get_nonminor_parents(self): # assumes have already marked the minor parents 
# according to current interests.
# otherwise, may remain marked according to a different seq, or possibly all on default value 
# (none are minor, all are important)
	potentials = copy(self.get_parents())
	nonminors = []
	while potentials:
		p = potentials.pop()
		if not p.is_minor:
			nonminors.append(p)
		else:
			potentials += p.get_parents()
	return list(set(nonminors))

@UnfinishedFunc
def get_nonminor_parent_sequences(self):
	return [p for p in self.get_nonminor_parents() if isinstance(p,UnfinishedSequence)]

@UnfinishedFunc
def get_immediate_parent_sequences(self): # gets both minor and nonminor sequences
	return [p for p in self.get_parents() if isinstance(p,UnfinishedSequence)]

@UnfinishedFunc
def pre_aggregate_comp(seq):
	vvars = seq.get_parent_sequences()
	vreal = zipmap(vvars,seq.elementwise_function)
	if isinstance(vreal,tuple): # equivalently, if seq.output_index >= 0:
		vreal = vreal[seq.output_index]
	return vreal

