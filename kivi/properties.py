#TODO: improve the properties module -- translate properteis into these classes.

class Property():
	def __init__(self, name):
		self.name = name


class Oscillation(Property):
	def __init__(self, name):
		super().__init__(name)


# This can be used for workload resources like deployment, statefulset, job and more.
class Workload(Property):
	def __init__(self, name):
		super().__init__(name)
		self.num_replicas_lower_bound = num_replicas_lower_bound
		self.num_replicas_upper_bound = num_replicas_upper_bound


	def to_promela(self):
		pass

class Pathlogicial(Property):
	def __init__(self, name):
		pass
