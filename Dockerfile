FROM leanprovercommunity/lean:latest

WORKDIR /app/

USER root

COPY lean-toolchain lakefile.lean lake-manifest.json EBPFSpec.lean ./ 
COPY EBPFSpec EBPFSpec/
#COPY . .

# Não faça chmod -R 777 aqui se der erro, apenas garanta que o usuário é root

RUN lake update
RUN lake build

CMD ["lake", "build"]
