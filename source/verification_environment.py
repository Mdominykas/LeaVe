from pathlib import Path
import shutil

from typeguard import typechecked

from config import CONF


class VerificationEnvironment:
    @typechecked
    def __init__(self, path: Path, source: Path, clear_past:bool = True):
        if clear_past and path.exists():
            shutil.rmtree(path)
        print("Makinsiu dira:", str(path))
        path.mkdir(parents=True, exist_ok=True)
        assert path.is_dir(), "A path to verification environment must a directory"
        self.verification_folder = path
        self.source = source


    # !!!! DOESN'T COPY THE PROD FILE
    def copy_actual_code(self, avoid_template: bool = False):
        found_template = False
        print("source is: ", self.source)
        for item in self.source.iterdir():
            if item.is_file():
                print("There was a file named: ", str(item.name))
                if str(item.name) == CONF.prodCircuitTemplate:
                    found_template = True
                    continue
                shutil.copy2(item, self.verification_folder / item.name)
        assert found_template or not avoid_template, "One should not copy the prod template"

    @typechecked
    def add_prod_template(self, prod_location: Path|None =None):
        if prod_location is None:
            prod_location = self.source / CONF.prodCircuitTemplate
        shutil.copy2(prod_location, self.verification_folder / CONF.prodCircuitTemplate)

    @typechecked
    def target_path(self) -> Path:
        return self.verification_folder

    @typechecked
    def target_str(self) -> str:
        return str(self.verification_folder.resolve())
    
    @typechecked
    def add_file(self, file_name: str, contents: str):
        with open(self.verification_folder / file_name , 'w') as f:
            f.write(contents)

    @typechecked
    def copy_file(self, file_path: Path, new_name: str):
        shutil.copy2(file_path, self.verification_folder / new_name)

    @typechecked
    def remove_file(self, file_name: str):
        file_path = self.target_path() / file_name
        file_path.unlink()