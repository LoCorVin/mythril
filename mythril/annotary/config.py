from json import loads, dumps
from os.path import dirname, realpath

class Config:
    def __init__(self, filepath=None):

        self.chain_verification = True
        self.depth = 3

        if filepath:
            with open(filepath) as config_file:
                config = loads(config_file.read())
                for k, v in config.items():
                    if hasattr(self,k):
                        setattr(self, k, v)

