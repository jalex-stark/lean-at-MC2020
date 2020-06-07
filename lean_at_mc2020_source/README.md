
- Copied (and modified) from https://github.com/avigad/mathematics_in_lean_source
  
- Run the following command to generate the document.
  
  ```
  make clean html examples latexpdf
  ```
  
- Source files are in the folder `source` output is in the folder `build`.

- **Todo:**
  
  
  -  Modify the path to pdf file, line 102 in `source/config.py`, when deploying
  
  	```
      'extra_nav_links': {'PDF version':'../latex/lean_at_mc2020.pdf',
  	```
  	
  - Modify `deploy.sh`
  
  - Check `source/config.py` 
  
  