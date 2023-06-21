
# make dir for results and temp usage
mkdir -p libs
mkdir -p results
mkdir -p temp

pip3 install -r requirements.txt

cd libs 
git clone "https://github.com/nimble-code/Spin.git"
cd Spin/Src
make