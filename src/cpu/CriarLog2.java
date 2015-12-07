/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package cpu;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author wellitongb
 */
public class CriarLog2 {
    private final File diretorio = new File("."); 
    private FileWriter arquivo;
    private PrintWriter output;
    
    /**
     *Método construtor da classe CriarLog1.
     * @param typeLog Representa o nome do algoritmo usado para criar o log.
     */
    public CriarLog2(String typeLog){
        openFile(typeLog);
        this.output.println("/*********************************");
        this.output.println("* Componentes do Grupo: ");
        this.output.println("* ELÍSIO BRENO GARCIA CARDOSO");
        this.output.println("* JOSÉ WELLITON NUNES JUNIOR");
        this.output.println("* MOISÉS CAVALCANTE FERNANDES");
        this.output.println("* VICTOR SANTIAGO VALENTE");
        this.output.println("**********************************/");
    }
    private void openFile(String typeLog){
        try{
            this.arquivo = new FileWriter(this.diretorio.getAbsolutePath().substring(0, this.diretorio.getAbsolutePath().length() - 1).concat(typeLog + " - LOG2.log"));
            this.output = new PrintWriter(this.arquivo);
        }
        catch (IOException ex) {
            System.out.println("Erro ao criar arquivo");
            Logger.getLogger(CriarLog1.class.getName()).log(Level.SEVERE, null, ex);
        }   
    }
    public void close(){
        this.output.close();
    }
    /**
     * Método que imprimi as informações do processo exigidas para o primeiro LOG.
     * @param filas Representa as filas de PRONTO,ESPERA,FINALIZADO.
     * @param timeSystem Representa o tempo do sistema.
     * @throws NullPointerException Caso filas seja nulo.
     * @throws Error Caso o tamanho de filas seja diferente de 3.
     */
    public void print(ArrayList<ArrayList<Processo>> filas, int timeSystem){
        if(filas == null){
            throw new NullPointerException("Não foi passado as filas exigidas para impressão");
        }
        if(filas.size() != 3){
            throw new Error("Não foi passado o numero de filas exigidas para impressão");
        }
        if(timeSystem%200 == 0){
            this.output.print(filas.get(0).size() + " ");
            this.output.print(filas.get(1).size() + " ");
            this.output.println(filas.get(2).size() + " ");
        }
    }
}
