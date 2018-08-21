from .ast_parser import get_contract_storage_members

def extract_storage_map(contract_ast):
    storage_members = get_contract_storage_members(contract_ast)
    print()
