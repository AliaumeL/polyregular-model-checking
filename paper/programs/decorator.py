
def list_function(func):
    def wrapper(*args, **kwargs):
        return list(func(*args, **kwargs))
    return wrapper