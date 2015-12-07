package cpu;

import java.io.File;

/**
 * Classe Principal que executa todo o projeto.
 * @author wellitongb
 */
public class CPU {

    /**
     * @param args the command line arguments
     */
    public static void main(String[] args) {
        File diretorio = new File("."); //objeto que cont�m o caminho do diretorio principal
        File arquivo = new File(diretorio.getAbsolutePath().substring(0, diretorio.getAbsolutePath().length() - 1).concat("processos.dat"));
        //objeto que cont�m o arquivo .dat a ser lido, no diretorio principal.
        Algorithm algorithm = new AlgorithmRR(arquivo.getAbsolutePath(), 123); // inicialização do objeto da classe AlgorithmRR
        algorithm.run(); // executa o algoritmo.
        algorithm.close(); // fecha os arquivos de logs criados.
        
        algorithm = new AlgorithmFCFS(arquivo.getAbsolutePath());// inicialização do objeto da classe AlgorithmFCFS
        algorithm.run(); // executa o algoritmo
        algorithm.close(); // fecha os arquivos de logs criados.
        
        algorithm = new AlgorithmSJF(arquivo.getAbsolutePath());// inicialização do objeto da classe AlgorithmSJF
        algorithm.run(); // executa o algoritmo.
        algorithm.close(); // fecha os arquivos de logs criados.
    }
    
}
